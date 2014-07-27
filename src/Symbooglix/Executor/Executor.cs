using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace Symbooglix
{

    public class Executor : IExecutorHandler
    {
        public enum HandlerAction 
        { 
            CONTINUE, // Allow execution of other handlers for this event
            STOP // Do not execute any more handlers for this event
        };
        
        public Executor(Program program, IStateScheduler scheduler, Solver.ISolver solver)
        { 
            this.TheProgram = program;
            StateScheduler = scheduler;
            SymbolicPool = new SymbolicPool();
            UninterpretedOrUninlinableFunctions = new List<Function>();
            PreEventHandlers = new List<IExecutorHandler>();
            PostEventHandlers = new List<IExecutorHandler>();
            BreakPointHandlers = new List<IBreakPointHandler>();
            TerminationHandlers = new List<ITerminationHandler>();
            CFT = new ConstantFoldingTraverser();
            UseConstantFolding = false;
            this.TheSolver = solver;
        }

        private IStateScheduler StateScheduler;
        public  ExecutionState CurrentState
        {
            get;
            private set;
        }

        private Program TheProgram;
        private ExecutionState InitialState; // Represents a state that has not entered any procedures
        private List<IExecutorHandler> PreEventHandlers;
        private List<IExecutorHandler> PostEventHandlers;
        private List<IBreakPointHandler> BreakPointHandlers;
        private List<ITerminationHandler> TerminationHandlers;
        private List<Function> UninterpretedOrUninlinableFunctions;
        private SymbolicPool SymbolicPool;
        private bool HasBeenPrepared = false;
        public ConstantFoldingTraverser CFT;
        public Solver.ISolver TheSolver;

        public bool UseConstantFolding
        {
            get;
            set;
        }


        public bool PrepareProgram(Transform.PassManager passManager = null)
        {
            if (passManager == null)
                passManager = new Transform.PassManager(TheProgram);

            passManager.Add(new Transform.FunctionInliningPass());
          
            // FIXME: Make this a pass
            // FIXME: Remove this? We aren't using it!
            // Make a list of all the functions that are uninterpreted or can't be inlined
            var functions = TheProgram.TopLevelDeclarations.OfType<Function>();
            foreach (var F in functions)
            {
                // bvbuiltins are interpreted as SMT-LIBv2 functions
                if (F.FindAttribute("bvbuiltin") != null)
                    continue;

                // Inlinable
                if (F.Body != null)
                    continue;

                UninterpretedOrUninlinableFunctions.Add(F);
                Debug.WriteLine("Added uninterpreted function " + F);
            }

            // Run our passes and any user requested passes
            passManager.Run();

            // Create initial execution state
            InitialState = CurrentState = new ExecutionState();

            // Load Global Variables and Constants
            var GVs = TheProgram.TopLevelDeclarations.OfType<Variable>().Where(g => g is GlobalVariable || g is Constant);
            var axioms = TheProgram.TopLevelDeclarations.OfType<Axiom>();
            foreach (Variable gv in GVs)
            {
                // Make symbolic
                var s = SymbolicPool.getFreshSymbolic(gv);
                Debug.Assert(!InitialState.Mem.Globals.ContainsKey(gv), "Cannot insert global that is already in memory");
                InitialState.Mem.Globals.Add(gv, s.Expr);
                InitialState.Symbolics.Add(s);

            }

            // Add the axioms as path constraints
            // We must do this before concretising any variables
            // otherwise we might end up adding constraints like
            // 0bv8 == 0bv8, instead of symbolic_0 == 0bv8
            foreach (var axiom in axioms)
            {
                var VMR = new VariableMapRewriter(InitialState);
                VMR.ReplaceGlobalsOnly = true; // The stackframe doesn't exist yet!
                Expr constraint = (Expr) VMR.Visit(axiom.Expr);
                InitialState.Constraints.AddConstraint(constraint);
                Debug.WriteLine("Adding constraint : " + constraint);
            }
             

            // See if we can concretise using the program's axioms
            foreach (var axiom in axioms)
            {
                LiteralExpr literal = null;
                Variable assignedTo = null;
                if (FindLiteralAssignment.findAnyVariable(axiom.Expr, out assignedTo, out literal))
                {
                    // Axioms should only be able to refer to globals
                    Debug.WriteLine("Concretising " + assignedTo.Name + " := " + literal.ToString());
                    Debug.Assert(InitialState.Mem.Globals.ContainsKey(assignedTo));
                    InitialState.Mem.Globals[assignedTo] = literal;
                }
            }


            HasBeenPrepared = true;

            // FIXME: check constraints are consistent!

            return true;
        }

        public void RegisterPreEventHandler(IExecutorHandler handler)
        {
            Debug.Assert(handler != null);
            PreEventHandlers.Add(handler);
        }

        public void UnregisterPreEventHandler(IExecutorHandler handler)
        {
            Debug.Assert(handler != null);
            Debug.Assert(PreEventHandlers.Contains(handler));
            PreEventHandlers.Remove(handler);
        }

        public void RegisterPostEventHandler(IExecutorHandler handler)
        {
            Debug.Assert(handler != null);
            PostEventHandlers.Add(handler);
        }

        public void UnregisterPostEventHandler(IExecutorHandler handler)
        {
            Debug.Assert(handler != null);
            Debug.Assert(PostEventHandlers.Contains(handler));
            PostEventHandlers.Remove(handler);
        }

        public void RegisterBreakPointHandler(IBreakPointHandler handler)
        {
            Debug.Assert(handler != null);
            BreakPointHandlers.Add(handler);
        }

        public void UnregisterBreakPointHandler(IBreakPointHandler handler)
        {
            Debug.Assert(handler != null);
            Debug.Assert(BreakPointHandlers.Contains(handler));
            BreakPointHandlers.Remove(handler);
        }

        public void RegisterTerminationHandler(ITerminationHandler handler)
        {
            Debug.Assert(handler != null);
            TerminationHandlers.Add(handler);
        }

        public void UnregisterTerminationHandler(ITerminationHandler handler)
        {
            Debug.Assert(handler != null);
            Debug.Assert(TerminationHandlers.Contains(handler));
            TerminationHandlers.Remove(handler);
        }

        public void Run(Implementation entryPoint)
        {
            if (!HasBeenPrepared)
                PrepareProgram();

            // FIXME: Clone initialState so we can deal with execution at a different entry point later on
            CurrentState = InitialState;

            StateScheduler.AddState(CurrentState);
            
            // FIXME: Check entry point is in prog?


            // Push entry point onto stack frame
            // FIXME: handle requires
            EnterImplementation(entryPoint,null, this);

            var oldState = CurrentState;
            while (StateScheduler.GetNumberOfStates() != 0)
            {
                CurrentState = StateScheduler.GetNextState();
                Debug.WriteLineIf(oldState != CurrentState, "[Switching context " + oldState.Id + " => " + CurrentState.Id + " ]");
                oldState = CurrentState;

                CurrentState.GetCurrentStackFrame().CurrentInstruction.MoveNext();
                ExecuteInstruction();
            }
            Console.WriteLine("Finished executing all states");

        }

        public void Terminate()
        {
            Console.WriteLine("Terminating early");
            Console.WriteLine("FIXME: Save state information");
            StateScheduler.RemoveAll(s => true);
            Debug.Assert(StateScheduler.GetNumberOfStates() == 0);
        }

        private void ExecuteInstruction()
        {
            Absy currentInstruction = CurrentState.GetCurrentStackFrame().CurrentInstruction.Current;
            if (currentInstruction == null)
                throw new NullReferenceException("Instruction was null");

            HandlerAction action = HandlerAction.CONTINUE;
            // Invoke pre-event handlers
            foreach (IExecutorHandler h in PreEventHandlers)
            {
                action = currentInstruction.visitCmd(h, this);
                if (action == HandlerAction.STOP)
                    return;
            }

            // Ignore the action returned from ourself
            currentInstruction.visitCmd(this, this); // Use double dispatch

            // Invoke post-event handlers
            foreach (IExecutorHandler h in PostEventHandlers)
            {
                action = currentInstruction.visitCmd(h, this);
                if (action == HandlerAction.STOP)
                    return;
            }
        }

        protected void HandleBreakPoints(PredicateCmd cmd) // FIXME: Support calls too!
        {
            string breakPointName = QKeyValue.FindStringAttribute(cmd.Attributes, "symbooglix_bp");
            if (breakPointName == null)
                return;

            HandlerAction action = HandlerAction.CONTINUE;
            foreach (IBreakPointHandler h in BreakPointHandlers)
            {
                action = h.handleBreakPoint(breakPointName, this);
                if (action == HandlerAction.STOP)
                    return;
            }
        }

        protected SymbolicVariable InitialiseAsSymbolic(Variable v)
        {
            Debug.Assert(CurrentState.IsInScopeVariable(v));
            var s = SymbolicPool.getFreshSymbolic(v);
            CurrentState.Symbolics.Add(s);
            CurrentState.AssignToVariableInScope(v, s.Expr);
            return s;
        }

        public SymbolicVariable MakeSymbolic(Variable v)
        {
            // FIXME: This needs to make a symbolic without an origin because it is a public API function
            throw new NotImplementedException();
        }

        public void MakeConcrete(Variable v, LiteralExpr literal)
        {
            Debug.Assert(CurrentState.IsInScopeVariable(v));
            Debug.Assert(IsSymbolic(v), "Tried to concretise something that is already concrete!");
            Debug.WriteLine("Concretising  {0} := {1}", v, literal);
            CurrentState.AssignToVariableInScope(v, literal);

            // FIXME: 
            // We can't remove this from the ExecutionState's set
            // of symbolic variables because it may of been propagated into other variables
            // We need a way of knowing if a symbolic has been propagated
            // and if not we should remove it
        }

        public bool IsSymbolic(Variable v)
        {
            // FIXME: When constant folding is fully implemented this check can be made REALLY fast
            // because anything that isn't a LiteralExpr must be symbolic after constant folding

            Debug.Assert(CurrentState.IsInScopeVariable(v), "Variable is not in scope");
            Expr e = CurrentState.GetInScopeVariableExpr(v);
            Debug.Assert(e != null , "Expression for variable is NULL");
            var fsv = new FindSymbolicsVisitor();
            fsv.Visit(e);
            return fsv.symbolics.Count != 0;
        }


        // if procedureParams == null then parameters will be assumed to be fresh symbolics
        // otherwise procedureParams should be a listof Expr for the procedure.
        // Note there is not need to make a copy of these Expr because a Boogie
        // procedure is not allowed to modify passed in parameters.
        public HandlerAction EnterImplementation(Implementation Impl, List<Expr> procedureParams, Executor executor)
        {
            // FIXME: The boundary between Executor and ExecutionState is
            // unclear, who should do the heavy lifting?
            CurrentState.EnterImplementation(Impl);

            // FIXME: We should check there are no name clashes between
            // existing program variables and symbolics

            // Load procedure in parameters on to stack
            if (procedureParams == null)
            {
                foreach (var v in Impl.InParams)
                {
                    CurrentState.GetCurrentStackFrame().Locals.Add(v, null); // Add dummy to stack so makeSymbolic works
                    InitialiseAsSymbolic(v);
                }
            }
            else
            {
                // Push expr for param on to stack.
                Debug.Assert(procedureParams.Count == Impl.InParams.Count);

                foreach (var tuple in Impl.InParams.Zip(procedureParams))
                {
                    CurrentState.GetCurrentStackFrame().Locals.Add(tuple.Item1, tuple.Item2);
                }

            }

            // Load procedure out parameters on to stack
            foreach(Variable v in Impl.OutParams)
            {
                // Make symbolic;
                CurrentState.GetCurrentStackFrame().Locals.Add(v, null);
                InitialiseAsSymbolic(v);
            }

            // Load procedure's declared locals on to stack
            foreach(Variable v in Impl.LocVars)
            {
                // Make symbolic
                CurrentState.GetCurrentStackFrame().Locals.Add(v, null);
                InitialiseAsSymbolic(v);
            }

            // Load procedure's requires statements as constraints.
            // We need to rewrite this expression before storing it because it may refer to 
            // procedure arguments rather than the implementation arguments which are confusingly
            // different instances of the same object.
            //
            // We also need to rewrite so that we remove any IdentifierExpr that refer to in program
            // variables and instead replace with expressions containing symbolic variables.
            var VR = new VariableMapRewriter(CurrentState);
            foreach (var VariablePair in Impl.InParams.Zip(Impl.Proc.InParams))
            {
                // Map Procedure InParams to Implementation InParams
                VR.preReplacementReMap.Add(VariablePair.Item2, VariablePair.Item1);
            }
            foreach (Requires r in Impl.Proc.Requires)
            {
                Expr constraint = (Expr) VR.Visit(r.Condition);

                // Check to see if the requires constraint is unsat
                // FIXME: This should probably be an option.
                TheSolver.SetConstraints(CurrentState.Constraints);
                Solver.Result result = TheSolver.IsQuerySat(constraint);

                if (result == Solver.Result.UNSAT)
                {
                    // We should not proceed because requires cannot be satisifed
                    CurrentState.MarkAsTerminatedEarly();

                    // notify the handlers
                    foreach (var handler in TerminationHandlers)
                        handler.handleUnsatisfiableRequires(CurrentState, r);

                    StateScheduler.RemoveState(CurrentState);
                    return HandlerAction.CONTINUE; // Should we prevent other handlers from executing?
                }

                CurrentState.Constraints.AddConstraint(constraint);
            }

            // Concretise globals and locals if explicitly set in requires statements
            foreach (Requires r in Impl.Proc.Requires)
            {
                Variable V = null;
                LiteralExpr literal = null;
                if (FindLiteralAssignment.findAnyVariable(r.Condition, out V, out literal))
                {
                    // HACK: For locals the requires statement attached to the procedure refer
                    // to arguments attached procedure and not to the implementation. This means we
                    // need to remap these Variables to implementation version when checking if a variable
                    // is in scope. Eurgh... We should fix Boogie instead to not do this!
                    if (VR.preReplacementReMap.ContainsKey(V))
                        V = VR.preReplacementReMap[V];

                    if (CurrentState.IsInScopeVariable(V))
                    {
                        MakeConcrete(V, literal);
                    }
                }
            }

            // FIXME: Check constraints are consistent

            return HandlerAction.CONTINUE;
        }

        public HandlerAction Handle(ReturnCmd c, Executor executor)
        {
            // Check ensures conditions, forking if necessary
            TheSolver.SetConstraints(CurrentState.Constraints);
            var VMR = new VariableMapRewriter(CurrentState);

            // FIXME: The variables attached to the procedure are not the same object instances
            // used for the procedure. Setup the mapping. Eurgh.. Boogie you suck!
            foreach (var tuple in CurrentState.GetCurrentStackFrame().Impl.Proc.InParams.Zip(CurrentState.GetCurrentStackFrame().Impl.InParams))
            {
                VMR.preReplacementReMap.Add(tuple.Item1, tuple.Item2);
            }
            foreach (var tuple in CurrentState.GetCurrentStackFrame().Impl.Proc.OutParams.Zip(CurrentState.GetCurrentStackFrame().Impl.OutParams))
            {
                VMR.preReplacementReMap.Add(tuple.Item1, tuple.Item2);
            }

            // Loop over each ensures to see if it can fail.
            foreach (var ensures in CurrentState.GetCurrentStackFrame().Impl.Proc.Ensures)
            {
                bool canFail = false;
                bool canSucceed = false;
                Expr remapped = VMR.Visit(ensures.Condition) as Expr;

                if (UseConstantFolding)
                    remapped = CFT.Traverse(remapped);

                // Constant folding might be able to avoid a solver call
                if (remapped is LiteralExpr)
                {
                    var literal = remapped as LiteralExpr;
                    Debug.Assert(literal.isBool, "ensures statement is not a bool!");

                    if (literal.IsTrue)
                    {
                        // No need to add "true" to the constraints
                        continue;
                    }
                    else if (literal.IsFalse)
                    {
                        // This state must fail
                        foreach (var handler in TerminationHandlers)
                            handler.handleFailingEnsures(CurrentState, ensures);

                        StateScheduler.RemoveState(CurrentState);
                        return HandlerAction.CONTINUE;
                    }
                    else
                    {
                        throw new InvalidProgramException("unreachable??");
                    }
                }

                // Can the ensures fail?
                Solver.Result result = TheSolver.IsNotQuerySat(remapped);
                switch (result)
                {
                    case Symbooglix.Solver.Result.SAT:
                        canFail = true;
                        break;
                    case Symbooglix.Solver.Result.UNSAT:
                        // This actually implies that
                        //
                        // ∀X : C(X) → Q(X)
                        // That is if the constraints are satisfiable then
                        // the query expr is always true. However I'm not sure
                        // if we can use this fact because we still need to check if the constraints
                        // can be satisfied
                        // FIXME: Do something about this!
                        break;
                    case Symbooglix.Solver.Result.UNKNOWN:
                        // Be conservative, may introduce false positives though.
                        canFail = true;
                        break;
                }

                // Can the ensures suceed?
                result = TheSolver.IsQuerySat(remapped);
                switch (result)
                {
                    case Solver.Result.SAT:
                        canSucceed = true;
                        break;
                    case Solver.Result.UNSAT:
                        break;
                    case Solver.Result.UNKNOWN:
                        // Be conservative, may explore infeasible path though
                        canSucceed = true;
                        break;
                }

                if (canFail && !canSucceed)
                {
                    // This state can only fail
                    CurrentState.MarkAsTerminatedEarly();

                    // notify handlers
                    foreach (var handler in TerminationHandlers)
                        handler.handleFailingEnsures(CurrentState, ensures);

                    StateScheduler.RemoveState(CurrentState);
                    return HandlerAction.CONTINUE;
                }
                else if (!canFail && canSucceed)
                {
                    // This state can only suceed
                    CurrentState.Constraints.AddConstraint(remapped);
                }
                else if (canFail && canSucceed)
                {
                    // This state can fail and suceed at the ensures
                    // fork both ways

                    var failedState = CurrentState.DeepClone();
                    failedState.MarkAsTerminatedEarly();

                    //notify handlers
                    foreach (var handler in TerminationHandlers)
                        handler.handleFailingEnsures(failedState, ensures);

                    // succesful state
                    CurrentState.Constraints.AddConstraint(remapped);
                }
                else
                {
                    throw new InvalidProgramException("Can't fail or succeed??");
                }
            }

            // Pass Parameters to Caller
            if (CurrentState.Mem.Stack.Count > 1)
            {
                StackFrame callingSF = CurrentState.Mem.Stack.ElementAt(CurrentState.Mem.Stack.Count - 2);
                CallCmd caller = (CallCmd) callingSF.CurrentInstruction.Current;
                Debug.Assert(caller is CallCmd);

                // Assign return parameters
                Debug.Assert(caller.Proc.OutParams.Count == caller.Outs.Count);
                foreach (var tuple in caller.Outs.Zip(CurrentState.GetCurrentStackFrame().Impl.OutParams))
                {
                    // Get return value
                    Expr value = CurrentState.GetInScopeVariableExpr(tuple.Item2);
                    Debug.Assert(value != null);

                    // Assign
                    CurrentState.AssignToVariableInStack(callingSF, tuple.Item1.Decl, value);
                }

            }

            // Pop stack frame
            CurrentState.LeaveImplementation();

            if (CurrentState.Finished())
            {
                // Notify any handlers that this state terminated without error
                foreach (var handler in TerminationHandlers)
                {
                    handler.handleSuccess(CurrentState);
                }

                StateScheduler.RemoveState(CurrentState);
            }

            return HandlerAction.CONTINUE;
     
        }


        public HandlerAction Handle(AssignCmd c, Executor executor)
        {
            int index=0;
            VariableMapRewriter r = new VariableMapRewriter(CurrentState);
            // FIXME: Should we zip asSimpleAssignCmd lhs and rhs instead?
            foreach(var lhsrhs in c.Lhss.Zip(c.Rhss))
            {
           
                Variable lvalue = lhsrhs.Item1.DeepAssignedVariable;
                Expr rvalue = null;

                // Check assignment allow
                Debug.Assert(lvalue.IsMutable, "lvalue is not mutable!");

                // Check lhs is actually in scope
                if (! CurrentState.IsInScopeVariable(lvalue))
                    throw new IndexOutOfRangeException("Lhs of assignment not in scope"); // FIXME: Wrong type of exception

                if (lhsrhs.Item1 is SimpleAssignLhs)
                {
                    // Duplicate and Expand out the expression so we only have symbolic identifiers in the expression
                    rvalue = (Expr) r.Visit(lhsrhs.Item2);
                    if (UseConstantFolding)
                        rvalue = CFT.Traverse(rvalue);
                }
                else if (lhsrhs.Item1 is MapAssignLhs)
                {
                    // We need to use "AsSimleAssignCmd" so that we have a single Variable as lhs and MapStore expressions
                    // on the right hand side
                    var ac = c.AsSimpleAssignCmd;
                    Debug.Assert(ac.Lhss[index].DeepAssignedVariable == lvalue, "lvalue mismatch");
                    rvalue = ac.Rhss[index];
                    // Duplicate and Expand out the expression so we only have symbolic identifiers in the expression
                    rvalue = (Expr) r.Visit(rvalue);

                    if (UseConstantFolding)
                        rvalue = CFT.Traverse(rvalue);
                }
                else
                {
                    throw new NotSupportedException("Unknown type of assignment");
                }

                CurrentState.AssignToVariableInScope(lvalue, rvalue);

                Debug.WriteLine("Assignment : " + lvalue + " := " + rvalue);
                ++index;
            }
            return HandlerAction.CONTINUE;
        }

        public HandlerAction Handle(AssertCmd c, Executor executor)
        {
            HandleBreakPoints(c);
            VariableMapRewriter r = new VariableMapRewriter(CurrentState);
            var dupAndrw = (Expr) r.Visit(c.Expr);

            if (UseConstantFolding)
                dupAndrw = CFT.Traverse(dupAndrw);

            Debug.WriteLine("Assert : " + dupAndrw);

            // Constant Folding might let us terminate without calling solver
            if (dupAndrw is LiteralExpr)
            {
                var literalAssertion = dupAndrw as LiteralExpr;
                Debug.Assert(literalAssertion.isBool);

                if (literalAssertion.IsTrue)
                {
                    // No need to add trivial "true" constraint
                    return HandlerAction.CONTINUE;
                }
                else if (literalAssertion.IsFalse)
                {
                    CurrentState.MarkAsTerminatedEarly();
                    // Notify our handlers
                    foreach (var handler in TerminationHandlers)
                    {
                        handler.handleFailingAssert(CurrentState);
                    }
                    StateScheduler.RemoveState(CurrentState);
                    return HandlerAction.CONTINUE;
                }
                else
                    throw new InvalidOperationException("Unreachable!"); // FIXME: We should define our exception types
            }

            TheSolver.SetConstraints(CurrentState.Constraints);


            // First see if it's possible for the assertion to fail
            Solver.Result result = TheSolver.IsNotQuerySat(dupAndrw);
            bool canFail = false;
            switch (result)
            {
                case Solver.Result.SAT:
                    canFail = true;
                    break;
                case Solver.Result.UNKNOWN:
                    Console.WriteLine("Error solver returned UNKNOWN"); // FIXME: Report this to some interface
                    canFail = true;
                    break;
                case Symbooglix.Solver.Result.UNSAT:
                    canFail = false;
                    break;
                default:
                    throw new InvalidOperationException("Invalid solver return code");
            }

            // Now see if it's possible for execution to continue past the assertion
            result = TheSolver.IsQuerySat(dupAndrw);
            bool canSucceed = false;
            switch (result)
            {
                case Solver.Result.SAT:
                    canSucceed = true;
                    break;
                case Solver.Result.UNKNOWN:
                    Console.WriteLine("Error solver returned UNKNOWN"); // FIXME: Report this to some interface
                    canSucceed = true;
                    break;
                case Symbooglix.Solver.Result.UNSAT:
                    canSucceed = false;
                    break;
                default:
                    throw new InvalidOperationException("Invalid solver return code");
            }

            if (canFail && !canSucceed)
            {
                // This state can only fail
                CurrentState.MarkAsTerminatedEarly();

                // Notify
                foreach (var handler in TerminationHandlers)
                    handler.handleFailingAssert(CurrentState);

                StateScheduler.RemoveState(CurrentState);
            }
            else if (!canFail && canSucceed)
            {
                // This state can only succeed
                CurrentState.Constraints.AddConstraint(dupAndrw);
            }
            else if (canFail && canSucceed)
            {
                // This state can fail and suceed at the current assertion

                // We need to fork and duplicate the states
                // Or do we? Copying the state just so we can inform
                // the handlers about it seems wasteful...
                ExecutionState failingState = CurrentState.DeepClone();
                failingState.MarkAsTerminatedEarly();

                // Notify
                foreach (var handler in TerminationHandlers)
                    handler.handleFailingAssert(failingState);

                // successful state can now have assertion expr in constraints
                CurrentState.Constraints.AddConstraint(dupAndrw);

            }
            else
            {
                throw new InvalidProgramException("Problem with solver");
            }


            return HandlerAction.CONTINUE;
        }

        public HandlerAction Handle(AssumeCmd c, Executor executor)
        {
            HandleBreakPoints(c);
            VariableMapRewriter r = new VariableMapRewriter(CurrentState);
            var dupAndrw = (Expr) r.Visit(c.Expr);

            if (UseConstantFolding)
                dupAndrw = CFT.Traverse(dupAndrw);

            Debug.WriteLine("Assume : " + dupAndrw);

            // Constant folding might let us terminate early without calling solver
            if (dupAndrw is LiteralExpr)
            {
                var literalAssumption = dupAndrw as LiteralExpr;
                Debug.Assert(literalAssumption.isBool);

                if (literalAssumption.IsTrue)
                {
                    // No need to add trivial "true" constraint
                    return HandlerAction.CONTINUE;
                }
                else if (literalAssumption.IsFalse)
                {
                    CurrentState.MarkAsTerminatedEarly();
                    // Notify our handlers
                    foreach (var handler in TerminationHandlers)
                    {
                        handler.handleUnsatisfiableAssume(CurrentState);
                    }
                    StateScheduler.RemoveState(CurrentState);
                    return HandlerAction.CONTINUE;
                }
            }

            TheSolver.SetConstraints(CurrentState.Constraints);
            Solver.Result result = TheSolver.IsQuerySat(dupAndrw);
            switch (result)
            {
                case Symbooglix.Solver.Result.UNSAT:
                    CurrentState.MarkAsTerminatedEarly();
                    // Notify our handlers
                    foreach (var handler in TerminationHandlers)
                    {
                        handler.handleUnsatisfiableAssume(CurrentState);
                    }
                    StateScheduler.RemoveState(CurrentState);
                    break;
                case Symbooglix.Solver.Result.SAT:
                    CurrentState.Constraints.AddConstraint(dupAndrw);
                    break;
                case Symbooglix.Solver.Result.UNKNOWN:
                    Console.WriteLine("Solver returned UNKNOWN!"); // FIXME: Report this to an interface.
                    CurrentState.Constraints.AddConstraint(dupAndrw);
                    break;
                default:
                    throw new InvalidOperationException("Invalid solver return code");
            }

            return HandlerAction.CONTINUE;
        }

        public HandlerAction Handle(GotoCmd c, Executor executor)
        {
            Debug.Assert(c.labelTargets.Count() > 0);

            if (c.labelTargets.Count() > 1)
            {
                ExecutionState newState = null;
                for (int targetId = 1, tEnd = c.labelTargets.Count; targetId < tEnd; ++targetId)
                {
                    // FIXME: We should look ahead for assumes and check that they are satisfiable so we don't create states and then immediatly destroy them!
                    newState = CurrentState.DeepClone(); // FIXME: This is not memory efficient
                    newState.GetCurrentStackFrame().TransferToBlock(c.labelTargets[targetId]);
                    StateScheduler.AddState(newState);
                }
            }

            // The current execution state will always take the first target
            CurrentState.GetCurrentStackFrame().TransferToBlock(c.labelTargets[0]);

            return HandlerAction.CONTINUE;
        }

        public HandlerAction Handle(CallCmd c, Executor executor)
        {
            var args = new List<Expr>();
            var reWritter = new VariableMapRewriter(CurrentState);

            // Find corresponding implementation
            var implementations = TheProgram.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Proc == c.Proc);
            Debug.Assert(implementations.Count() == 1);
            Implementation imp = implementations.First();

            foreach (Expr e in c.Ins)
            {
                args.Add( (Expr) reWritter.Visit(e) );
            }

            HandlerAction action = HandlerAction.CONTINUE;
            foreach (IExecutorHandler h in PreEventHandlers)
            {
                action = h.EnterImplementation(imp, args, this);
                if (action == HandlerAction.STOP)
                    break;
            }

            // We have slightly different semantics here to the handle() methods. Clients cannot block enterProcedure()
            EnterImplementation(imp, args, this);
            foreach (IExecutorHandler h in PostEventHandlers)
            {
                action = h.EnterImplementation(imp, args, this);
                if (action == HandlerAction.STOP)
                    break;
            }
            return HandlerAction.CONTINUE;
        }

        public HandlerAction Handle(AssertEnsuresCmd c, Executor executor)
        {
            throw new NotImplementedException ();
            //return HandlerAction.CONTINUE;
        }

        public HandlerAction Handle(AssertRequiresCmd c, Executor executor)
        {
            throw new NotImplementedException ();
            //return HandlerAction.CONTINUE;
        }

        public HandlerAction Handle(HavocCmd c, Executor executor)
        {
            Debug.WriteLine("Havoc : " + c.ToString().TrimEnd('\n'));
            for (int index=0; index < c.Vars.Count ; ++index)
            {
                var s = SymbolicPool.getFreshSymbolic(c, index);
                Debug.Assert(CurrentState.IsInScopeVariable(c.Vars[index]), "Havoc variable is not in scope");
                CurrentState.AssignToVariableInScope(c.Vars[index].Decl, s.Expr);
                CurrentState.Symbolics.Add(s);

            }
            return HandlerAction.CONTINUE;
        }

        public HandlerAction Handle(YieldCmd c, Executor executor)
        {
            throw new NotImplementedException ();
            //return HandlerAction.CONTINUE;
        }

    }
}

