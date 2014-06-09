using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace symbooglix
{

    public class Executor : IExecutorHandler
    {
        public enum HandlerAction 
        { 
            CONTINUE, // Allow execution of other handlers for this event
            STOP // Do not execute any more handlers for this event
        };
        
        public Executor(Program prog, IStateScheduler scheduler, Solver.ISolver solver)
        { 
            this.prog = prog;
            stateScheduler = scheduler;
            symbolicPool = new SymbolicPool();
            UninterpretedOrUninlinableFunctions = new List<Function>();
            preEventHandlers = new List<IExecutorHandler>();
            postEventHandlers = new List<IExecutorHandler>();
            breakPointHandlers = new List<IBreakPointHandler>();
            terminationHandlers = new List<ITerminationHandler>();
            CFT = new ConstantFoldingTraverser();
            UseConstantFolding = false;
            this.solver = solver;
        }

        private IStateScheduler stateScheduler;
        public  ExecutionState currentState
        {
            get;
            private set;
        }
        private Program prog;
        private ExecutionState initialState; // Represents a state that has not entered any procedures
        private List<IExecutorHandler> preEventHandlers;
        private List<IExecutorHandler> postEventHandlers;
        private List<IBreakPointHandler> breakPointHandlers;
        private List<ITerminationHandler> terminationHandlers;
        private List<Function> UninterpretedOrUninlinableFunctions;
        private SymbolicPool symbolicPool;
        private bool hasBeenPrepared = false;
        public ConstantFoldingTraverser CFT;
        public Solver.ISolver solver;

        public bool UseConstantFolding
        {
            get;
            set;
        }


        public bool prepareProgram()
        {
            // Create initial execution state
            initialState = currentState = new ExecutionState();

            // Make a list of all the functions that are uninterpreted or can't be inlined
            var functions = prog.TopLevelDeclarations.OfType<Function>();
            foreach (var F in functions)
            {
                // bvbuiltins are interpreted as SMT-LIBv2 functions
                if (F.FindAttribute("bvbuiltin") != null)
                    continue;

                // FIXME: When we support inling, skip those functions that we would later inline

                UninterpretedOrUninlinableFunctions.Add(F);
                Debug.WriteLine("Added uninterpreted function " + F);
            }

            // Inform the solver of these functions
            solver.SetFunctions(UninterpretedOrUninlinableFunctions);

            // Load Global Variables and Constants
            var GVs = prog.TopLevelDeclarations.OfType<Variable>().Where(g => g is GlobalVariable || g is Constant);
            var axioms = prog.TopLevelDeclarations.OfType<Axiom>();
            foreach (Variable gv in GVs)
            {
                // Make symbolic
                var s = symbolicPool.getFreshSymbolic(gv);
                Debug.Assert(!initialState.mem.globals.ContainsKey(gv), "Cannot insert global that is already in memory");
                initialState.mem.globals.Add(gv, s.expr);
                initialState.symbolics.Add(s);

            }

            // Add the axioms as path constraints
            // We must do this before concretising any variables
            // otherwise we might end up adding constraints like
            // 0bv8 == 0bv8, instead of symbolic_0 == 0bv8
            foreach (var axiom in axioms)
            {
                var VMR = new VariableMapRewriter(initialState);
                VMR.ReplaceGlobalsOnly = true; // The stackframe doesn't exist yet!
                Expr constraint = (Expr) VMR.Visit(axiom.Expr);
                initialState.cm.addConstraint(constraint);
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
                    Debug.Assert(initialState.mem.globals.ContainsKey(assignedTo));
                    initialState.mem.globals[assignedTo] = literal;
                }
            }


            hasBeenPrepared = true;

            // FIXME: check constraints are consistent!

            return true;
        }

        public void registerPreEventHandler(IExecutorHandler handler)
        {
            Debug.Assert(handler != null);
            preEventHandlers.Add(handler);
        }

        public void unregisterPreEventHandler(IExecutorHandler handler)
        {
            Debug.Assert(handler != null);
            Debug.Assert(preEventHandlers.Contains(handler));
            preEventHandlers.Remove(handler);
        }

        public void registerPostEventHandler(IExecutorHandler handler)
        {
            Debug.Assert(handler != null);
            postEventHandlers.Add(handler);
        }

        public void unregisterPostEventHandler(IExecutorHandler handler)
        {
            Debug.Assert(handler != null);
            Debug.Assert(postEventHandlers.Contains(handler));
            postEventHandlers.Remove(handler);
        }

        public void registerBreakPointHandler(IBreakPointHandler handler)
        {
            Debug.Assert(handler != null);
            breakPointHandlers.Add(handler);
        }

        public void unregisterBreakPointHandler(IBreakPointHandler handler)
        {
            Debug.Assert(handler != null);
            Debug.Assert(breakPointHandlers.Contains(handler));
            breakPointHandlers.Remove(handler);
        }

        public void registerTerminationHandler(ITerminationHandler handler)
        {
            Debug.Assert(handler != null);
            terminationHandlers.Add(handler);
        }

        public void unregisterTerminationHandler(ITerminationHandler handler)
        {
            Debug.Assert(handler != null);
            Debug.Assert(terminationHandlers.Contains(handler));
            terminationHandlers.Remove(handler);
        }

        public void run(Implementation entryPoint)
        {
            if (!hasBeenPrepared)
                prepareProgram();

            // FIXME: Clone initialState so we can deal with execution at a different entry point later on
            currentState = initialState;

            stateScheduler.addState(currentState);
            
            // FIXME: Check entry point is in prog?


            // Push entry point onto stack frame
            // FIXME: handle requires
            enterProcedure(entryPoint,null, this);

            var oldState = currentState;
            while (stateScheduler.getNumberOfStates() != 0)
            {
                currentState = stateScheduler.getNextState();
                Debug.WriteLineIf(oldState != currentState, "[Switching context]");
                oldState = currentState;

                currentState.getCurrentStackFrame().currentInstruction.MoveNext();
                executeInstruction();
            }
            Console.WriteLine("Finished executing all states");

        }

        public void terminate()
        {
            Console.WriteLine("Terminating early");
            Console.WriteLine("FIXME: Save state information");
            stateScheduler.removeAll(s => true);
            Debug.Assert(stateScheduler.getNumberOfStates() == 0);
        }

        private void executeInstruction()
        {
            Absy currentInstruction = currentState.getCurrentStackFrame().currentInstruction.Current;
            if (currentInstruction == null)
                throw new NullReferenceException("Instruction was null");

            HandlerAction action = HandlerAction.CONTINUE;
            // Invoke pre-event handlers
            foreach (IExecutorHandler h in preEventHandlers)
            {
                action = currentInstruction.visitCmd(h, this);
                if (action == HandlerAction.STOP)
                    return;
            }

            // Ignore the action returned from ourself
            currentInstruction.visitCmd(this, this); // Use double dispatch

            // Invoke post-event handlers
            foreach (IExecutorHandler h in postEventHandlers)
            {
                action = currentInstruction.visitCmd(h, this);
                if (action == HandlerAction.STOP)
                    return;
            }
        }

        protected void handleBreakPoints(PredicateCmd cmd) // FIXME: Support calls too!
        {
            string breakPointName = QKeyValue.FindStringAttribute(cmd.Attributes, "symbooglix_bp");
            if (breakPointName == null)
                return;

            HandlerAction action = HandlerAction.CONTINUE;
            foreach (IBreakPointHandler h in breakPointHandlers)
            {
                action = h.handleBreakPoint(breakPointName, this);
                if (action == HandlerAction.STOP)
                    return;
            }
        }

        protected SymbolicVariable initialiseAsSymbolic(Variable v)
        {
            Debug.Assert(currentState.isInScopeVariable(v));
            var s = symbolicPool.getFreshSymbolic(v);
            currentState.symbolics.Add(s);
            currentState.assignToVariableInScope(v, s.expr);
            return s;
        }

        public SymbolicVariable makeSymbolic(Variable v)
        {
            // FIXME: This needs to make a symbolic without an origin because it is a public API function
            throw new NotImplementedException();
        }

        public void makeConcrete(Variable v, LiteralExpr literal)
        {
            Debug.Assert(currentState.isInScopeVariable(v));
            Debug.Assert(isSymbolic(v), "Tried to concretise something that is already concrete!");
            Debug.WriteLine("Concretising  {0} := {1}", v, literal);
            currentState.assignToVariableInScope(v, literal);

            // FIXME: 
            // We can't remove this from the ExecutionState's set
            // of symbolic variables because it may of been propagated into other variables
            // We need a way of knowing if a symbolic has been propagated
            // and if not we should remove it
        }

        public bool isSymbolic(Variable v)
        {
            // FIXME: When constant folding is fully implemented this check can be made REALLY fast
            // because anything that isn't a LiteralExpr must be symbolic after constant folding

            Debug.Assert(currentState.isInScopeVariable(v), "Variable is not in scope");
            Expr e = currentState.getInScopeVariableExpr(v);
            Debug.Assert(e != null , "Expression for variable is NULL");
            var fsv = new FindSymbolicsVisitor();
            fsv.Visit(e);
            return fsv.symbolics.Count != 0;
        }


        // if procedureParams == null then parameters will be assumed to be fresh symbolics
        // otherwise procedureParams should be a listof Expr for the procedure.
        // Note there is not need to make a copy of these Expr because a Boogie
        // procedure is not allowed to modify passed in parameters.
        public HandlerAction enterProcedure(Implementation Impl, List<Expr> procedureParams, Executor executor)
        {
            // FIXME: The boundary between Executor and ExecutionState is
            // unclear, who should do the heavy lifting?
            currentState.enterProcedure(Impl);

            // FIXME: We should check there are no name clashes between
            // existing program variables and symbolics

            // Load procedure in parameters on to stack
            if (procedureParams == null)
            {
                foreach (var v in Impl.InParams)
                {
                    currentState.getCurrentStackFrame().locals.Add(v, null); // Add dummy to stack so makeSymbolic works
                    initialiseAsSymbolic(v);
                }
            }
            else
            {
                // Push expr for param on to stack.
                Debug.Assert(procedureParams.Count == Impl.InParams.Count);

                foreach (var tuple in Impl.InParams.Zip(procedureParams))
                {
                    currentState.getCurrentStackFrame().locals.Add(tuple.Item1, tuple.Item2);
                }

            }

            // Load procedure out parameters on to stack
            foreach(Variable v in Impl.OutParams)
            {
                // Make symbolic;
                currentState.getCurrentStackFrame().locals.Add(v, null);
                initialiseAsSymbolic(v);
            }

            // Load procedure's declared locals on to stack
            foreach(Variable v in Impl.LocVars)
            {
                // Make symbolic
                currentState.getCurrentStackFrame().locals.Add(v, null);
                initialiseAsSymbolic(v);
            }

            // Load procedure's requires statements as constraints.
            // We need to rewrite this expression before storing it because it may refer to 
            // procedure arguments rather than the implementation arguments which are confusingly
            // different instances of the same object.
            //
            // We also need to rewrite so that we remove any IdentifierExpr that refer to in program
            // variables and instead replace with expressions containing symbolic variables.
            var VR = new VariableMapRewriter(currentState);
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
                solver.SetConstraints(currentState.cm);
                Solver.Result result = solver.IsQuerySat(constraint);

                if (result == Solver.Result.UNSAT)
                {
                    // We should not proceed because requires cannot be satisifed
                    currentState.MarkAsTerminatedEarly();

                    // notify the handlers
                    foreach (var handler in terminationHandlers)
                        handler.handleUnsatisfiableRequires(currentState, r);

                    stateScheduler.removeState(currentState);
                    return HandlerAction.CONTINUE; // Should we prevent other handlers from executing?
                }

                currentState.cm.addConstraint(constraint);
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

                    if (currentState.isInScopeVariable(V))
                    {
                        makeConcrete(V, literal);
                    }
                }
            }

            // FIXME: Check constraints are consistent

            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(ReturnCmd c, Executor executor)
        {
            // Check ensures conditions, forking if necessary
            solver.SetConstraints(currentState.cm);
            var VMR = new VariableMapRewriter(currentState);

            // FIXME: The variables attached to the procedure are not the same object instances
            // used for the procedure. Setup the mapping. Eurgh.. Boogie you suck!
            foreach (var tuple in currentState.getCurrentStackFrame().procedure.Proc.InParams.Zip(currentState.getCurrentStackFrame().procedure.InParams))
            {
                VMR.preReplacementReMap.Add(tuple.Item1, tuple.Item2);
            }
            foreach (var tuple in currentState.getCurrentStackFrame().procedure.Proc.OutParams.Zip(currentState.getCurrentStackFrame().procedure.OutParams))
            {
                VMR.preReplacementReMap.Add(tuple.Item1, tuple.Item2);
            }

            // Loop over each ensures to see if it can fail.
            foreach (var ensures in currentState.getCurrentStackFrame().procedure.Proc.Ensures)
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
                        foreach (var handler in terminationHandlers)
                            handler.handleFailingEnsures(currentState, ensures);

                        stateScheduler.removeState(currentState);
                        return HandlerAction.CONTINUE;
                    }
                    else
                    {
                        throw new InvalidProgramException("unreachable??");
                    }
                }

                // Can the ensures fail?
                Solver.Result result = solver.IsNotQuerySat(remapped);
                switch (result)
                {
                    case symbooglix.Solver.Result.SAT:
                        canFail = true;
                        break;
                    case symbooglix.Solver.Result.UNSAT:
                        // This actually implies that
                        //
                        // ∀X : C(X) → Q(X)
                        // That is if the constraints are satisfiable then
                        // the query expr is always true. However I'm not sure
                        // if we can use this fact because we still need to check if the constraints
                        // can be satisfied
                        // FIXME: Do something about this!
                        break;
                    case symbooglix.Solver.Result.UNKNOWN:
                        // Be conservative, may introduce false positives though.
                        canFail = true;
                        break;
                }

                // Can the ensures suceed?
                result = solver.IsQuerySat(remapped);
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
                    currentState.MarkAsTerminatedEarly();

                    // notify handlers
                    foreach (var handler in terminationHandlers)
                        handler.handleFailingEnsures(currentState, ensures);

                    stateScheduler.removeState(currentState);
                    return HandlerAction.CONTINUE;
                }
                else if (!canFail && canSucceed)
                {
                    // This state can only suceed
                    currentState.cm.addConstraint(remapped);
                }
                else if (canFail && canSucceed)
                {
                    // This state can fail and suceed at the ensures
                    // fork both ways

                    var failedState = currentState.DeepClone();
                    failedState.MarkAsTerminatedEarly();

                    //notify handlers
                    foreach (var handler in terminationHandlers)
                        handler.handleFailingEnsures(failedState, ensures);

                    // succesful state
                    currentState.cm.addConstraint(remapped);
                }
                else
                {
                    throw new InvalidProgramException("Can't fail or succeed??");
                }
            }

            // Pass Parameters to Caller
            if (currentState.mem.stack.Count > 1)
            {
                StackFrame callingSF = currentState.mem.stack.ElementAt(currentState.mem.stack.Count - 2);
                CallCmd caller = (CallCmd) callingSF.currentInstruction.Current;
                Debug.Assert(caller is CallCmd);

                // Assign return parameters
                Debug.Assert(caller.Proc.OutParams.Count == caller.Outs.Count);
                foreach (var tuple in caller.Outs.Zip(currentState.getCurrentStackFrame().procedure.OutParams))
                {
                    // Get return value
                    Expr value = currentState.getInScopeVariableExpr(tuple.Item2);
                    Debug.Assert(value != null);

                    // Assign
                    currentState.assignToVariableInStack(callingSF, tuple.Item1.Decl, value);
                }

            }

            // Pop stack frame
            currentState.leaveProcedure();

            if (currentState.finished())
            {
                // Notify any handlers that this state terminated without error
                foreach (var handler in terminationHandlers)
                {
                    handler.handleSuccess(currentState);
                }

                stateScheduler.removeState(currentState);
            }

            return HandlerAction.CONTINUE;
     
        }


        public HandlerAction handle(AssignCmd c, Executor executor)
        {
            int index=0;
            VariableMapRewriter r = new VariableMapRewriter(currentState);
            // FIXME: Should we zip asSimpleAssignCmd lhs and rhs instead?
            foreach(var lhsrhs in c.Lhss.Zip(c.Rhss))
            {
           
                Variable lvalue = lhsrhs.Item1.DeepAssignedVariable;
                Expr rvalue = null;

                // Check assignment allow
                Debug.Assert(lvalue.IsMutable, "lvalue is not mutable!");

                // Check lhs is actually in scope
                if (! currentState.isInScopeVariable(lvalue))
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

                currentState.assignToVariableInScope(lvalue, rvalue);

                Debug.WriteLine("Assignment : " + lvalue + " := " + rvalue);
                ++index;
            }
            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(AssertCmd c, Executor executor)
        {
            handleBreakPoints(c);
            VariableMapRewriter r = new VariableMapRewriter(currentState);
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
                    currentState.MarkAsTerminatedEarly();
                    // Notify our handlers
                    foreach (var handler in terminationHandlers)
                    {
                        handler.handleFailingAssert(currentState);
                    }
                    stateScheduler.removeState(currentState);
                    return HandlerAction.CONTINUE;
                }
                else
                    throw new InvalidOperationException("Unreachable!"); // FIXME: We should define our exception types
            }

            solver.SetConstraints(currentState.cm);
            Solver.IAssignment assignment = null;

            // First see if it's possible for the assertion to fail
            Solver.Result result = solver.IsNotQuerySat(dupAndrw, out assignment);
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
                case symbooglix.Solver.Result.UNSAT:
                    canFail = false;
                    break;
                default:
                    throw new InvalidOperationException("Invalid solver return code");
            }

            // Now see if it's possible for execution to continue past the assertion
            Solver.IAssignment successfulAssignment;
            result = solver.IsQuerySat(dupAndrw, out successfulAssignment);
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
                case symbooglix.Solver.Result.UNSAT:
                    canSucceed = false;
                    break;
                default:
                    throw new InvalidOperationException("Invalid solver return code");
            }

            if (canFail && !canSucceed)
            {
                // This state can only fail
                currentState.MarkAsTerminatedEarly();

                // Notify
                foreach (var handler in terminationHandlers)
                    handler.handleFailingAssert(currentState);

                stateScheduler.removeState(currentState);
            }
            else if (!canFail && canSucceed)
            {
                // This state can only succeed
                currentState.cm.addConstraint(dupAndrw);
            }
            else if (canFail && canSucceed)
            {
                // This state can fail and suceed at the current assertion

                // We need to fork and duplicate the states
                // Or do we? Copying the state just so we can inform
                // the handlers about it seems wasteful...
                ExecutionState failingState = currentState.DeepClone();
                failingState.MarkAsTerminatedEarly();

                // Notify
                foreach (var handler in terminationHandlers)
                    handler.handleFailingAssert(failingState);

                // successful state can now have assertion expr in constraints
                currentState.cm.addConstraint(dupAndrw);

            }
            else
            {
                throw new InvalidProgramException("Problem with solver");
            }


            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(AssumeCmd c, Executor executor)
        {
            handleBreakPoints(c);
            VariableMapRewriter r = new VariableMapRewriter(currentState);
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
                    currentState.MarkAsTerminatedEarly();
                    // Notify our handlers
                    foreach (var handler in terminationHandlers)
                    {
                        handler.handleUnsatisfiableAssume(currentState);
                    }
                    stateScheduler.removeState(currentState);
                    return HandlerAction.CONTINUE;
                }
            }

            solver.SetConstraints(currentState.cm);
            Solver.Result result = solver.IsQuerySat(dupAndrw);
            switch (result)
            {
                case symbooglix.Solver.Result.UNSAT:
                    currentState.MarkAsTerminatedEarly();
                    // Notify our handlers
                    foreach (var handler in terminationHandlers)
                    {
                        handler.handleUnsatisfiableAssume(currentState);
                    }
                    stateScheduler.removeState(currentState);
                    break;
                case symbooglix.Solver.Result.SAT:
                    currentState.cm.addConstraint(dupAndrw);
                    break;
                case symbooglix.Solver.Result.UNKNOWN:
                    Console.WriteLine("Solver returned UNKNOWN!"); // FIXME: Report this to an interface.
                    currentState.cm.addConstraint(dupAndrw);
                    break;
                default:
                    throw new InvalidOperationException("Invalid solver return code");
            }

            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(GotoCmd c, Executor executor)
        {
            Debug.Assert(c.labelTargets.Count() > 0);

            if (c.labelTargets.Count() > 1)
            {
                ExecutionState newState = null;
                for (int targetId = 1, tEnd = c.labelTargets.Count; targetId < tEnd; ++targetId)
                {
                    // FIXME: We should look ahead for assumes and check that they are satisfiable so we don't create states and then immediatly destroy them!
                    newState = currentState.DeepClone(); // FIXME: This is not memory efficient
                    newState.getCurrentStackFrame().transferToBlock(c.labelTargets[targetId]);
                    stateScheduler.addState(newState);
                }
            }

            // The current execution state will always take the first target
            currentState.getCurrentStackFrame().transferToBlock(c.labelTargets[0]);

            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(CallCmd c, Executor executor)
        {
            var args = new List<Expr>();
            var reWritter = new VariableMapRewriter(currentState);

            // Find corresponding implementation
            var implementations = prog.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Proc == c.Proc);
            Debug.Assert(implementations.Count() == 1);
            Implementation imp = implementations.First();

            foreach (Expr e in c.Ins)
            {
                args.Add( (Expr) reWritter.Visit(e) );
            }

            HandlerAction action = HandlerAction.CONTINUE;
            foreach (IExecutorHandler h in preEventHandlers)
            {
                action = h.enterProcedure(imp, args, this);
                if (action == HandlerAction.STOP)
                    break;
            }

            // We have slightly different semantics here to the handle() methods. Clients cannot block enterProcedure()
            enterProcedure(imp, args, this);
            foreach (IExecutorHandler h in postEventHandlers)
            {
                action = h.enterProcedure(imp, args, this);
                if (action == HandlerAction.STOP)
                    break;
            }
            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(AssertEnsuresCmd c, Executor executor)
        {
            throw new NotImplementedException ();
            //return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(AssertRequiresCmd c, Executor executor)
        {
            throw new NotImplementedException ();
            //return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(HavocCmd c, Executor executor)
        {
            Debug.WriteLine("Havoc : " + c.ToString().TrimEnd('\n'));
            for (int index=0; index < c.Vars.Count ; ++index)
            {
                var s = symbolicPool.getFreshSymbolic(c, index);
                Debug.Assert(currentState.isInScopeVariable(c.Vars[index]), "Havoc variable is not in scope");
                currentState.assignToVariableInScope(c.Vars[index].Decl, s.expr);
                currentState.symbolics.Add(s);

            }
            return HandlerAction.CONTINUE;
        }

        public HandlerAction handle(YieldCmd c, Executor executor)
        {
            throw new NotImplementedException ();
            //return HandlerAction.CONTINUE;
        }

    }
}

