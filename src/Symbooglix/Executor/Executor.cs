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

        // Events
        public class BreakPointEventArgs : EventArgs
        {
            public readonly string Name;
            public BreakPointEventArgs(string name) {this.Name = name;}
        }
        public delegate void BreakPointEvent(Object executor, BreakPointEventArgs data);
        public event BreakPointEvent BreakPointReached;

        public class ExecutionStateEventArgs : EventArgs
        {
            public readonly ExecutionState State;
            public ExecutionStateEventArgs(ExecutionState e) { State = e;}
        }
        public delegate void ExecutionStateEvent(Object executor, ExecutionStateEventArgs data);

        public event ExecutionStateEvent StateTerminated;

        public bool PrepareProgram(Transform.PassManager passManager = null)
        {
            if (passManager == null)
                passManager = new Transform.PassManager(TheProgram);

            if (passManager.TheProgram != TheProgram)
                throw new InvalidOperationException("PassManager must use same program as executor");

            var FRF = new FindRecursiveFunctionsPass();
            passManager.Add(FRF);
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

            // Don't allow recursive function for now as we can't handle them!
            if (FRF.RecursiveFunctions.Count > 0)
            {
                Console.ForegroundColor = ConsoleColor.Red;
                Console.Error.WriteLine("Detected the following recursive functions");
                foreach (var function in FRF.RecursiveFunctions)
                {
                    Console.Error.Write(function.Name + ": ");
                    if (function.Body != null)
                        Console.Error.WriteLine(function.Body.ToString());

                    if (function.DefinitionAxiom != null)
                        Console.Error.WriteLine(function.DefinitionAxiom.Expr.ToString());
                }
                Console.ResetColor();

                throw new NotSupportedException("Cannot handle recursive functions");
            }

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

        public void Run(Implementation entryPoint)
        {
            if (!HasBeenPrepared)
                PrepareProgram();

            // Clone the state so we can keep the special initial state around
            // if we want run() to be called again with a different entry point.
            CurrentState = InitialState.DeepClone();

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

            if (BreakPointReached != null)
                BreakPointReached(this, new BreakPointEventArgs(breakPointName));
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


        // if implementationParams == null then parameters will be assumed to be fresh symbolics
        // otherwise procedureParams should be a listof Expr for the procedure.
        // Note there is not need to make a copy of these Expr because a Boogie
        // procedure is not allowed to modify passed in parameters.
        public HandlerAction EnterImplementation(Implementation Impl, List<Expr> implementationParams, Executor executor)
        {
            bool isProgramEntryPoint = CurrentState.Mem.Stack.Count == 0;

            // FIXME: The boundary between Executor and ExecutionState is
            // unclear, who should do the heavy lifting?
            CurrentState.EnterImplementation(Impl);

            // FIXME: We should check there are no name clashes between
            // existing program variables and symbolics

            // Load procedure in parameters on to stack
            if (implementationParams == null)
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
                Debug.Assert(implementationParams.Count == Impl.InParams.Count);

                foreach (var tuple in Impl.InParams.Zip(implementationParams))
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
            bool stillInState = true;
            var VR = new VariableMapRewriter(CurrentState);
            foreach (var VariablePair in Impl.InParams.Zip(Impl.Proc.InParams))
            {
                // Map Procedure InParams to Implementation InParams
                VR.preReplacementReMap.Add(VariablePair.Item2, VariablePair.Item1);
            }
            foreach (Requires r in Impl.Proc.Requires)
            {
                Expr constraint = (Expr) VR.Visit(r.Condition);

                // We need to treat the semantics of requires differently depening on where
                // we are
                if (isProgramEntryPoint)
                {
                    // On entry we treat requires like an assume so it constrains
                    // the initial state
                    HowToTerminateState helper = delegate(ExecutionState theStateThatWillBeTerminated)
                    {
                        theStateThatWillBeTerminated.Terminate(new TerminatedAtUnsatisfiableEntryRequires(r));
                    };

                    stillInState = HandleAssumeLikeCommand(constraint, helper);
                }
                else
                {
                    // We want to treat requires like an assert so that we follow
                    // path where the requires expression isn't satisfied by the
                    // caller
                    HowToTerminateState helper = delegate(ExecutionState theStateThatWillBeTerminated)
                    {
                        theStateThatWillBeTerminated.Terminate(new TerminatedAtFailingRequires(r));
                    };

                    stillInState = HandleAssertLikeCommand(constraint, helper);
                }

                if (!stillInState)
                {
                    // The current state was destroyed so we can't continue handling this command
                    return HandlerAction.CONTINUE;
                }

            }

            // We presume now that the CurrentState wasn't destroyed so its safe to continue
            Debug.Assert(stillInState && !CurrentState.Finished(), "Can't continue to enter procedure of terminated state!");

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
            return HandlerAction.CONTINUE;
        }

        public HandlerAction EnterAndLeaveProcedure(Procedure proc, List<Expr> procedureParams, Executor executor)
        {
            Debug.Assert(CurrentState.Mem.Stack.Count > 0, "Can't enter a procedure without first entering an implementation");
            StackFrame callingStackFrame = CurrentState.GetCurrentStackFrame();

            // Add a dummy stack frame
            CurrentState.Mem.Stack.Add(new StackFrame(proc));


            // Add input parameters on to dummy stack.
            Debug.Assert(procedureParams.Count == proc.InParams.Count);
            foreach (var tuple in proc.InParams.Zip(procedureParams))
            {
                CurrentState.GetCurrentStackFrame().Locals.Add(tuple.Item1, tuple.Item2);
            }

            // Add output parameters on to dummy stack as new symbolic variables
            foreach(Variable v in proc.OutParams)
            {
                // Make symbolic;
                CurrentState.GetCurrentStackFrame().Locals.Add(v, null);
                InitialiseAsSymbolic(v);
            }

            // Assert each requires (this might produce failing states)
            bool stillInState = true;
            var VR = new VariableMapRewriter(CurrentState);

            // We don't need to do any of that nasty preReplacementReMap
            // stuff here because there is no implementation
            foreach (var requires in proc.Requires)
            {
                Expr condition = (Expr) VR.Visit(requires.Condition);

                HowToTerminateState helper = delegate(ExecutionState theStateThatWillBeTerminated)
                {
                    theStateThatWillBeTerminated.Terminate(new TerminatedAtFailingRequires(requires));
                };

                stillInState = HandleAssertLikeCommand(condition, helper);
            }

            // Check we're still in state
            if (!stillInState)
            {
                // The CurrentState was terminated so we can't continue
                Debug.Assert(CurrentState.Finished());
                return HandlerAction.CONTINUE;
            }

            // Make the Global variables in Modset Symbolic
            for (int modSetIndex=0;  modSetIndex < proc.Modifies.Count ; ++modSetIndex)
            {
                var symbolic = SymbolicPool.getFreshSymbolic(proc, modSetIndex);
                CurrentState.AssignToVariableInScope(proc.Modifies[modSetIndex].Decl, symbolic.Expr);
                CurrentState.Symbolics.Add(symbolic);
            }

            // Assume each ensures
            foreach (var ensures in proc.Ensures)
            {
                Expr condition = (Expr) VR.Visit(ensures.Condition);

                // FIXME: We should add an option to disable this because we might want to blindly
                // assume without checking if its feasible.
                HowToTerminateState helper = delegate(ExecutionState theStateThatWillBeTerminated)
                {
                    theStateThatWillBeTerminated.Terminate(new TerminatedAtUnsatisfiableEnsures(ensures));
                };

                stillInState = HandleAssumeLikeCommand(condition, helper);
            }

            // Check we're still in state
            if (!stillInState)
            {
                // The CurrentState was terminated so we can't continue
                Debug.Assert(CurrentState.Finished());
                return HandlerAction.CONTINUE;
            }
                
            // Put return parameters into callee's stack frame
            Debug.Assert(callingStackFrame.CurrentInstruction.Current is CallCmd, "Expected the calling stack frame's current instruction to be a CallCmd");
            var caller = callingStackFrame.CurrentInstruction.Current as CallCmd;

            // Assign return parameters
            Debug.Assert(caller.Proc == proc);
            Debug.Assert(proc.OutParams.Count == caller.Outs.Count);
            foreach (var tuple in caller.Outs.Zip(proc.OutParams))
            {
                // Get return value
                Expr value = CurrentState.GetInScopeVariableExpr(tuple.Item2);
                Debug.Assert(value != null);

                // Assign. Try globals first
                Variable varToAssignTo = tuple.Item1.Decl;
                if (varToAssignTo is GlobalVariable)
                {
                    CurrentState.AssignToGlobalVariable(varToAssignTo as GlobalVariable, value);
                }
                else
                {
                    bool success = CurrentState.AssignToVariableInStack(callingStackFrame, tuple.Item1.Decl, value);
                    Debug.Assert(success, "Could not assign to local variable");
                }
            }

            // Pop the dummy stack
            CurrentState.Mem.PopStackFrame();

            return HandlerAction.CONTINUE;
        }

        public HandlerAction Handle(ReturnCmd c, Executor executor)
        {
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
            bool stillInCurrentState = true;
            foreach (var ensures in CurrentState.GetCurrentStackFrame().Impl.Proc.Ensures)
            {
                Expr remapped = VMR.Visit(ensures.Condition) as Expr;

                if (UseConstantFolding)
                    remapped = CFT.Traverse(remapped);

                // Note we use closure to pass the ensures we are currently looking at
                HowToTerminateState helper = delegate(ExecutionState theStateThatWillBeTerminated)
                {
                    theStateThatWillBeTerminated.Terminate(new TerminatedAtFailingEnsures(ensures));
                };
                // Treat an requires similarly to an assert
                stillInCurrentState = HandleAssertLikeCommand(remapped, helper);

                if (!stillInCurrentState)
                {
                    // The current state was destroyed because an ensures always failed
                    // so we shouldn't try to continue execution of it.
                    return HandlerAction.CONTINUE;
                }
            }

            // We presume it is now safe to continue with the return
            Debug.Assert(stillInCurrentState && !executor.CurrentState.Finished() , "Cannot do a return if the currentState was terminated!");

            // Pass Parameters to Caller
            if (CurrentState.Mem.Stack.Count > 1)
            {
                StackFrame callingSF = CurrentState.Mem.Stack.ElementAt(CurrentState.Mem.Stack.Count - 2);
                Debug.Assert(callingSF.CurrentInstruction.Current is CallCmd, "Expected the calling stack frame's current instruction to be a CallCmd");
                var caller = callingSF.CurrentInstruction.Current as CallCmd;

                // Assign return parameters
                Debug.Assert(caller.Proc.OutParams.Count == caller.Outs.Count);
                foreach (var tuple in caller.Outs.Zip(CurrentState.GetCurrentStackFrame().Impl.OutParams))
                {
                    // Get return value
                    Expr value = CurrentState.GetInScopeVariableExpr(tuple.Item2);
                    Debug.Assert(value != null);

                    // Assign
                    var varToAssignTo = tuple.Item1.Decl;
                    if (varToAssignTo is GlobalVariable)
                    {
                        CurrentState.AssignToGlobalVariable(varToAssignTo as GlobalVariable, value);
                    }
                    else
                    {
                        bool success = CurrentState.AssignToVariableInStack(callingSF, tuple.Item1.Decl, value);
                        Debug.Assert(success, "Failed to assign to variable in stack");
                    }
                }

            }

            // Pop stack frame
            CurrentState.LeaveImplementation();

            // If the stack frame is empty after poping the previous stack then we have
            // finished execution of the current state.
            if (CurrentState.Mem.Stack.Count == 0)
            {
                CurrentState.Terminate(new TerminatedWithoutError(c));

                // Notify
                if (StateTerminated!= null)
                    StateTerminated(this, new ExecutionStateEventArgs(CurrentState));

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

            // Create an anonymous method to tell the helper function
            // how to terminate the state
            HowToTerminateState helper = delegate(ExecutionState theStateThatWillBeTerminated)
            {
                // Mark the state as terminated
                theStateThatWillBeTerminated.Terminate(new TerminatedAtFailingAssert(c));
            };

            // Use helper method, we don't need to care if the current state is destroyed
            HandleAssertLikeCommand(dupAndrw, helper);
            return HandlerAction.CONTINUE;
        }

        protected delegate void HowToTerminateState(ExecutionState theStateThatWillBeTerminated);
        protected bool HandleAssertLikeCommand(Expr condition, HowToTerminateState terminate)
        {
            // Constant Folding might let us terminate without calling solver
            if (condition is LiteralExpr)
            {
                var literalAssertion = condition as LiteralExpr;
                Debug.Assert(literalAssertion.isBool);

                if (literalAssertion.IsTrue)
                {
                    // No need to add trivial "true" constraint
                    return true; // Still in a state
                }
                else if (literalAssertion.IsFalse)
                {
                    // Terminate the state
                    terminate(CurrentState);

                    // Notify
                    if (StateTerminated != null)
                        StateTerminated(this, new ExecutionStateEventArgs(CurrentState));

                    StateScheduler.RemoveState(CurrentState);
                    return false; // No longer in a state because removed the current state
                }
                else
                    throw new InvalidOperationException("Unreachable!"); // FIXME: We should define our own exception types
            }

            TheSolver.SetConstraints(CurrentState.Constraints);

            // First see if it's possible for the assertion/ensures to fail
            // ∃ X constraints(X) ∧ ¬ condition(X)
            Solver.Result result = TheSolver.IsNotQuerySat(condition);
            bool canFail = false;
            bool canSucceed = false;
            bool canNeverFail = false;
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
                    // This actually implies that
                    //
                    // ∀X : C(X) → Q(X)
                    // That is if the constraints are satisfiable then
                    // the query expr is always true. Because we've been
                    // checking constraints as we go we already know C(X) is satisfiable
                    canFail = false;
                    canNeverFail = true;
                    break;
                default:
                    throw new InvalidOperationException("Invalid solver return code");
            }

            // Only invoke solver again if necessary
            if (canNeverFail)
            {
                // In this case the assert/ensures will always succeed
                // so no need to call solver to ask if this is the case.
                canSucceed = true;
            }
            else
            {
                // Now see if it's possible for execution to continue past the assertion
                // ∃ X constraints(X) ∧ condition(X)
                result = TheSolver.IsQuerySat(condition);
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
            }

            if (canFail && !canSucceed)
            {
                terminate(CurrentState);

                // Notify
                if (StateTerminated != null)
                    StateTerminated(this, new ExecutionStateEventArgs(CurrentState));

                StateScheduler.RemoveState(CurrentState);
                return false; // No longer in a state because we removed the current state
            }
            else if (!canFail && canSucceed)
            {
                // This state can only succeed
                CurrentState.Constraints.AddConstraint(condition);
                return true; // We are still in the current state
            }
            else if (canFail && canSucceed)
            {
                // This state can fail and suceed at the current assertion/ensures

                // We need to fork and duplicate the states
                // Or do we? Copying the state just so we can inform
                // the handlers about it seems wasteful...
                ExecutionState failingState = CurrentState.DeepClone();
                terminate(failingState);

                // Notify
                if (StateTerminated != null)
                    StateTerminated(this, new ExecutionStateEventArgs(failingState));

                // successful state can now have assertion expr in constraints
                CurrentState.Constraints.AddConstraint(condition);
                return true; // We are still in the current state
            }
            else
            {
                throw new InvalidProgramException("Problem with solver");
            }
        }

        protected bool HandleAssumeLikeCommand(Expr condition, HowToTerminateState terminate)
        {
            // Constant folding might let us terminate early without calling solver
            if (condition is LiteralExpr)
            {
                var literalAssumption = condition as LiteralExpr;
                Debug.Assert(literalAssumption.isBool);

                if (literalAssumption.IsTrue)
                {
                    // No need to add trivial "true" constraint
                    return true; // We didn't destroy a state
                }
                else if (literalAssumption.IsFalse)
                {
                    terminate(CurrentState);

                    // Notify
                    if (StateTerminated != null)
                        StateTerminated(this, new ExecutionStateEventArgs(CurrentState));

                    StateScheduler.RemoveState(CurrentState);
                    return false; // No longer in current state
                }
            }

            // Is it possible for the condition to be satisfied
            // ∃ X : constraints(X) ∧ condition(X)
            TheSolver.SetConstraints(CurrentState.Constraints);
            Solver.Result result = TheSolver.IsQuerySat(condition);
            switch (result)
            {
                case Symbooglix.Solver.Result.UNSAT:
                    terminate(CurrentState);

                    // Notify
                    if (StateTerminated != null)
                        StateTerminated(this, new ExecutionStateEventArgs(CurrentState));

                    StateScheduler.RemoveState(CurrentState);
                    return false; // No longer in current state

                case Symbooglix.Solver.Result.SAT:
                    CurrentState.Constraints.AddConstraint(condition);
                    break;
                case Symbooglix.Solver.Result.UNKNOWN:
                    Console.WriteLine("Solver returned UNKNOWN!"); // FIXME: Report this to an interface.
                    // Be conservative and just add the constraint
                    // FIXME: Is this a bug? HandleAssertLikeCmd() assumes that current constraints are satisfiable
                    CurrentState.Constraints.AddConstraint(condition);
                    break;
                default:
                    throw new InvalidOperationException("Invalid solver return code");
            }
            return true; // We are still in the current state
        }

        public HandlerAction Handle(AssumeCmd c, Executor executor)
        {
            HandleBreakPoints(c);
            VariableMapRewriter r = new VariableMapRewriter(CurrentState);
            var dupAndrw = (Expr) r.Visit(c.Expr);

            if (UseConstantFolding)
                dupAndrw = CFT.Traverse(dupAndrw);

            Debug.WriteLine("Assume : " + dupAndrw);

            HowToTerminateState helper = delegate(ExecutionState theStateThatWillBeTerminated)
            {
                // Terminate the state
                theStateThatWillBeTerminated.Terminate(new TerminatedAtUnsatisfiableAssume(c));
            };

            // Use helper. We don't care if it terminates a state because we immediatly return afterwards
            HandleAssumeLikeCommand(dupAndrw, helper);
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
            Implementation impl = null;

            var implementations = TheProgram.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Proc == c.Proc);
            if (implementations.Count() > 0)
            {
                // FIXME: What if there is more than one implementation?
                impl = implementations.First();
            }

            foreach (Expr e in c.Ins)
            {
                args.Add( (Expr) reWritter.Visit(e) );
            }

            // FIXME: All this handler stuff is gross. Remove it!
            if (impl != null)
            {
                HandlerAction action = HandlerAction.CONTINUE;
                foreach (IExecutorHandler h in PreEventHandlers)
                {
                    action = h.EnterImplementation(impl, args, this);
                    if (action == HandlerAction.STOP)
                        break;
                }

                // We have slightly different semantics here to the handle() methods. Clients cannot block EnterImplementation()
                EnterImplementation(impl, args, this);
                foreach (IExecutorHandler h in PostEventHandlers)
                {
                    action = h.EnterImplementation(impl, args, this);
                    if (action == HandlerAction.STOP)
                        break;
                }
            }
            else
            {
                HandlerAction action = HandlerAction.CONTINUE;
                foreach (IExecutorHandler h in PreEventHandlers)
                {
                    action = h.EnterAndLeaveProcedure(c.Proc, args, this);
                    if (action == HandlerAction.STOP)
                        break;
                }

                // We have slightly different semantics here to the handle() methods. Clients cannot block EnterAndLeaveProcedure()
                EnterAndLeaveProcedure(c.Proc, args, this);
                foreach (IExecutorHandler h in PostEventHandlers)
                {
                    action = h.EnterAndLeaveProcedure(c.Proc, args, this);
                    if (action == HandlerAction.STOP)
                        break;
                }
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

