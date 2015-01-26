using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace Symbooglix
{

    public class Executor : Util.IYAMLWriter
    {
        public Executor(Program program, IStateScheduler scheduler, Solver.ISolver solver, IExprBuilder builder)
        { 
            this.TheProgram = program;
            StateScheduler = scheduler;
            SymbolicPool = new SymbolicPool();
            UseGotoLookAhead = true;
            UseGlobalDDE = true;
            this.TheSolver = solver;
            this.Duplicator = new BuilderDuplicator(builder);
            this.InternalRequestedEntryPoints = new List<Implementation>();
            this.InternalStatistics.Reset();
            this.RunTimer = new Stopwatch();
            this.PrepareTimer = new Stopwatch();
            this.InternalPreparationPassManager = new Transform.PassManager();
            AssertFilter = null;
            this.TerminationType = ExecutorTerminationType.UNKNOWN;
            HasBeenPrepared = false;
            this.Builder = builder;
        }

        private IStateScheduler StateScheduler;
        private BuilderDuplicator Duplicator;
        private IExprBuilder Builder;
        public  ExecutionState CurrentState
        {
            get;
            private set;
        }


        public Program TheProgram;
        private ExecutionState InitialState; // Represents a state that has not entered any procedures
        private SymbolicPool SymbolicPool;
        public bool HasBeenPrepared
        {
            get;
            private set;
        }
        public ConstantFoldingTraverser CFT;
        public Solver.ISolver TheSolver;
        private bool AllowExecutorToRun= false;
        public Predicate<AssertCmd> AssertFilter
        {
            get;
            set;
        }

        public bool UseGotoLookAhead
        {
            get;
            set;
        }

        public bool UseGlobalDDE
        {
            get;
            set;
        }

        private List<Implementation> InternalRequestedEntryPoints;

        public IEnumerable<Implementation> RequestedEntryPoints
        {
            get { return InternalRequestedEntryPoints; }
        }

        private ExecutorStatistics InternalStatistics;
        private Stopwatch RunTimer;
        private Stopwatch PrepareTimer;
        public ExecutorStatistics Statistics
        {
            get
            {
                UpdateStatistics();
                return InternalStatistics;
            }
        }

        private void UpdateStatistics()
        {
            InternalStatistics.RunTime = RunTimer.Elapsed;
            InternalStatistics.PrepareTime = PrepareTimer.Elapsed;
        }

        // Events
        public class BreakPointEventArgs : EventArgs
        {
            public readonly string Name;
            public BreakPointEventArgs(string name) {this.Name = name;}
        }
        public event EventHandler<BreakPointEventArgs> BreakPointReached;

        public class ExecutionStateEventArgs : EventArgs
        {
            public readonly ExecutionState State;
            public ExecutionStateEventArgs(ExecutionState e) { State = e;}
        }
        public event EventHandler<ExecutionStateEventArgs> StateTerminated;

        public event EventHandler<ExecutionStateEventArgs> NonTerminatedStateRemoved;

        public enum ExecutorTerminationType
        {
            UNKNOWN,
            FINISHED,
            TIMEOUT,
            OUT_OF_MEMORY
        }

        public ExecutorTerminationType TerminationType
        {
            get
            {
                return InternalStatistics.TerminationType;
            }
            private set
            {
                InternalStatistics.TerminationType = value;
            }
        }

        public class ExecutorTerminatedArgs : EventArgs
        {
            public readonly ExecutorTerminationType TerminationType;
            public ExecutorTerminatedArgs(Executor theExecutor)
            {
                TerminationType = theExecutor.TerminationType;
            }
        }

        public class ExecutorTimeoutReachedArgs : EventArgs
        {
            // Empty for now
        }

        public class ExecutorStartedArgs : EventArgs
        {
            // Empty right now
        }
        public event EventHandler<ExecutorTerminatedArgs> ExecutorTerminated;
        public event EventHandler<ExecutorStartedArgs> ExecutorStarted;
        public event EventHandler<ExecutorTimeoutReachedArgs> ExecutorTimeoutReached;

        public class InstructionVisitEventArgs : EventArgs
        {
            public readonly ProgramLocation Location;
            public InstructionVisitEventArgs(ProgramLocation location) {this.Location = location;}
        }
        public event EventHandler<InstructionVisitEventArgs> InstructionVisited;

        public class EnterProcedureEventArgs : EventArgs
        {
            public readonly Procedure Proc = null;
            public readonly List<Expr> Args = null;
            public EnterProcedureEventArgs(Procedure proc, List<Expr> args)
            {
                this.Proc = proc;
                this.Args = new List<Expr>();
                foreach (var arg in args)
                    Args.Add(arg);
            }
        }

        public class LeaveProcedureEventArgs : EventArgs
        {
            public readonly Procedure Proc = null;
            public LeaveProcedureEventArgs(Procedure proc)
            {
                this.Proc = proc;
            }
        }

        public class EnterImplementationEventArgs : EventArgs
        {
            public readonly Implementation Impl = null;
            public readonly List<Expr> Args = null;
            public EnterImplementationEventArgs(Implementation impl, List<Expr> args)
            {
                this.Impl = impl;

                if (args == null)
                    return;

                this.Args = new List<Expr>();
                foreach (var arg in args)
                    Args.Add(arg);
            }
        }

        public class LeaveImplementationEventArgs : EventArgs
        {
            public readonly Implementation Impl = null;
            public LeaveImplementationEventArgs(Implementation impl)
            {
                this.Impl = impl;
            }
        }

        public event EventHandler<EnterProcedureEventArgs> ProcedureEntered;
        public event EventHandler<EnterImplementationEventArgs> ImplementationEntered;
        public event EventHandler<LeaveProcedureEventArgs> ProcedureLeft;
        public event EventHandler<LeaveImplementationEventArgs> ImplementationLeft;

        public class ContextChangeEventArgs : EventArgs
        {
            public readonly ExecutionState Previous;
            public readonly ExecutionState Next;
            public ContextChangeEventArgs(ExecutionState previous, ExecutionState next)
            {
                this.Previous = previous;
                this.Next = next;
            }
        }

        public event EventHandler<ContextChangeEventArgs> ContextChanged;

        public ExecutionTreeNode TreeRoot
        {
            get
            {
                if (InitialState == null)
                    return null;
                else
                    return InitialState.TreeNode;
            }
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            // General Executor stats
            Statistics.WriteAsYAML(TW);
            TW.WriteLine("prepared: {0}", HasBeenPrepared.ToString().ToLower());
            TW.WriteLine("use_global_dde: {0}", UseGlobalDDE.ToString().ToLower());
            TW.WriteLine("use_goto_look_ahead: {0}", UseGotoLookAhead.ToString().ToLower());

            TW.WriteLine("state_scheduler:");
            TW.Indent += 1;
            StateScheduler.WriteAsYAML(TW);
            TW.Indent -= 1;

            TW.WriteLine("solver:");
            TW.Indent += 1;
            TheSolver.Statistics.WriteAsYAML(TW);
            TW.Indent -= 1;

            TW.WriteLine("solver_impl:");
            TW.Indent += 1;
            TheSolver.SolverImpl.Statistics.WriteAsYAML(TW);
            TW.Indent -= 1;
        }

        private bool PrepareProgram()
        {
            PrepareTimer.Start();

            if (HasBeenPrepared)
                return true;

            var FRF = new FindRecursiveFunctionsPass();
            InternalPreparationPassManager.Add(FRF);
            InternalPreparationPassManager.Add(new Transform.FunctionInliningPass());

            if (UseGlobalDDE)
                InternalPreparationPassManager.Add(new Transform.GlobalDeadDeclEliminationPass());

            InternalPreparationPassManager.Add(new Transform.OldExprCanonicaliser());
            InternalPreparationPassManager.Add(new Transform.UniqueVariableEnforcingPass());

            // We need ProgramLocation annotations to work out where stuff comes from
            InternalPreparationPassManager.Add(new Annotation.ProgramLocationAnnotater());

            // For profiling Boogie Program execution
            InternalPreparationPassManager.Add(new Annotation.InstructionStatisticsAnnotater());

            // Run our passes and any user requested passes
            InternalPreparationPassManager.Run(TheProgram);

            // Don't allow recursive function for now as we can't handle them!
            if (FRF.RecursiveFunctions.Count > 0)
            {
                throw new RecursiveFunctionDetectedException(this, FRF.RecursiveFunctions);
            }

            // Create initial execution state
            InitialState = CurrentState = new ExecutionState();

            // Load Global Variables and Constants
            var GVs = TheProgram.TopLevelDeclarations.OfType<Variable>().Where(g => g is GlobalVariable || g is Constant);
            var axioms = TheProgram.TopLevelDeclarations.OfType<Axiom>();
            foreach (Variable gv in GVs)
            {
                if (gv.TypedIdent.WhereExpr != null)
                    throw new NotImplementedException("WhereExpr on globals not supported");

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
                axiom.GetInstructionStatistics().IncrementCovered();
                ++InternalStatistics.InstructionsExecuted; // Increment now just in case we return early

                // Check The axiom can be satisfied
                TheSolver.SetConstraints(InitialState.Constraints);

                var VMR = new MapExecutionStateVariablesDuplicator(InitialState, this.Builder);
                VMR.ReplaceGlobalsOnly = true; // The stackframe doesn't exist yet!

                Expr constraint = (Expr) VMR.Visit(axiom.Expr);

                Solver.Result result = TheSolver.IsQuerySat(constraint);
                switch (result)
                {
                    case Symbooglix.Solver.Result.SAT:
                        break;
                    case Symbooglix.Solver.Result.UNSAT:
                        goto default;
                    case Symbooglix.Solver.Result.UNKNOWN:
                        InitialState.MakeSpeculative();
                        goto default; // Eurgh...
                    default:
                        var terminatedAtUnsatisfiableAxiom = new TerminatedAtUnsatisfiableAxiom(axiom);
                        terminatedAtUnsatisfiableAxiom.ConditionForUnsat = constraint;

                        // Expr.Not(constraint) will only be satisfiable if
                        // the original constraints are satisfiable
                        // i.e. ¬ ∃ x constraints(x) ∧ query(x) implies that
                        // ∀ x constraints(x) ∧ ¬query(x)
                        // So here we assume
                        terminatedAtUnsatisfiableAxiom.ConditionForSat = Expr.Not(constraint);

                        TerminateState(InitialState, terminatedAtUnsatisfiableAxiom, /*removeFromStateScheduler=*/false);
                        HasBeenPrepared = true; // Don't allow this method to run again
                        PrepareTimer.Stop();
                        return false;
                }

                InitialState.Constraints.AddConstraint(constraint, axiom.GetProgramLocation());
                Debug.WriteLine("Adding constraint : " + constraint);

                // See if we can concretise using the program's axioms
                // Note we must use Expr that is not remapped (i.e. must contain original program variables)
                LiteralExpr literal = null;
                Variable assignedTo = null;
                var axiomExprToCheckForLiteralAssignment = axiom.Expr;

                // Note: The duplicator being used here uses a Builder so this gives an opportunity to do constant folding
                axiomExprToCheckForLiteralAssignment =  (Expr) Duplicator.Visit(axiom.Expr);

                if (FindLiteralAssignment.findAnyVariable(axiomExprToCheckForLiteralAssignment, out assignedTo, out literal))
                {
                    // Axioms should only be able to refer to globals
                    Debug.WriteLine("Concretising " + assignedTo.Name + " := " + literal.ToString());
                    Debug.Assert(InitialState.Mem.Globals.ContainsKey(assignedTo), "Cannot assign to global variable not in global memory");
                    InitialState.Mem.Globals[assignedTo] = literal;
                }
            }


            HasBeenPrepared = true;
            PrepareTimer.Stop();
            return true;
        }


        private Transform.PassManager InternalPreparationPassManager;
        public Transform.PassManager PreparationPassManager
        {
            get
            {
                return InternalPreparationPassManager;
            }
            set
            {
                // The PassManager should not be changed during execution
                lock (ExecutorLoopLock)
                {
                    InternalPreparationPassManager = value;
                }
            }
        }

        protected void SetupTimeout(int timeout)
        {
            if (timeout <= 0)
                return;

            // Create a thread that will kill the executor after the timeout is hit.
            Task.Factory.StartNew(() =>
            {
                Thread.Sleep(timeout * 1000); // argument is in milliseconds
                this.TerminationType = ExecutorTerminationType.TIMEOUT;
                // Notify
                if (ExecutorTimeoutReached != null)
                {
                    var eventArg = new ExecutorTimeoutReachedArgs();
                    ExecutorTimeoutReached(this, eventArg );
                }

                this.Terminate();
            }, TaskCreationOptions.LongRunning);
        }

        public void Run(Implementation entryPoint, int timeout=0)
        {
            // This lock exists for two reasons
            // 1. Force calls to this method to be serialised.
            // 2. Allows the Terminate() method to block on this method.
            lock (ExecutorLoopLock)
            {
                List<char> preAllocated = null;

                OutOfMemoryException oome = null;

                try
                {
                    // HACK: pre-allocate 10MiB that we can free if we run out of memory
                    // to allow us to do clean up
                    preAllocated = new List<char>(10 << 20);
                    preAllocated.Add('a'); // Prevent not-used warning
                    InternalRun(entryPoint, timeout);
                }
                catch (OutOfMemoryException e)
                {
                    Console.Error.WriteLine("Executor ran out of memory!");
                    preAllocated = null; // Remove "root" to this so GC can clean up
                    System.GC.Collect();
                    this.TerminationType = ExecutorTerminationType.OUT_OF_MEMORY;
                    oome = e;
                }
                finally
                {
                    Console.WriteLine("Notifying listeners of Executor termination");
                    // Notify listeners that the Executor finished.


                    // If we ran out of memory the hope is that we free'd enough
                    // for the listeners to be able to complete but this is not guaranteed.
                    if (ExecutorTerminated != null)
                    {
                        ExecutorTerminated(this, new ExecutorTerminatedArgs(this));
                    }
                }

                // Now that we've finished notifying, rethrow the exception if necessary
                if (oome != null)
                    throw oome;
            }
        }

        private Object ExecutorLoopLock = new object();
        private void InternalRun(Implementation entryPoint, int timeout=0)
        {
            AllowExecutorToRun = true;
            RunTimer.Start();
            SetupTimeout(timeout);

            // Record the entry point that was requested
            InternalRequestedEntryPoints.Add(entryPoint);

            if (!HasBeenPrepared)
                PrepareProgram();

            // Notify
            if (ExecutorStarted != null)
                ExecutorStarted(this, new ExecutorStartedArgs());

            if (InitialState.Finished())
            {
                if (ExecutorTerminated != null)
                    ExecutorTerminated(this, new ExecutorTerminatedArgs(this));

                throw new ExecuteTerminatedStateException(this, InitialState);
            }

            // Clone the state so we can keep the special initial state around
            // if we want run() to be called again with a different entry point.
            CurrentState = Fork(InitialState, null);
            --InternalStatistics.ForkCount; // We don't want the forking of the initial state to be counted as a fork

            StateScheduler.ReceiveExecutor(this);
            StateScheduler.AddState(CurrentState);

            // Check the provided entry point is actually in the program we are about to execute
            if (TheProgram.TopLevelDeclarations.OfType<Implementation>().Where(impl => impl == entryPoint).Count() == 0)
            {
                throw new InvalidEntryPoint(this, entryPoint);
            }

            // Push entry point onto stack frame
            EnterImplementation(entryPoint, null);

            var oldState = CurrentState;
            while (AllowExecutorToRun)
            {
                CurrentState = StateScheduler.GetNextState();
                if (CurrentState == null)
                {
                    // No states left
                    break;
                }

                if (CurrentState.Speculative)
                {
                    // FIXME: Report hiting a speculative execution state as an event!
                    Console.WriteLine("Not executing a speculative Execution State!");
                    this.TerminateState(CurrentState, new TerminatedWithDisallowedSpeculativePath());
                    continue;
                }

                Debug.Assert(!CurrentState.Finished(), "Cannot execute a terminated state!");

                // Notify that the Executed state has changed.
                if (ContextChanged != null & oldState != CurrentState)
                    ContextChanged(this, new ContextChangeEventArgs(oldState, CurrentState));

                oldState = CurrentState;

                CurrentState.GetCurrentStackFrame().CurrentInstruction.MoveNext();
                ExecuteInstruction();
            }

            // Remove any remaining states and notify about them
            while (StateScheduler.GetNumberOfStates() > 0)
            {
                var state = StateScheduler.GetNextState();
                StateScheduler.RemoveState(state);

                if (NonTerminatedStateRemoved != null)
                    NonTerminatedStateRemoved(this, new ExecutionStateEventArgs(state));

            }

            if (this.TerminationType == ExecutorTerminationType.UNKNOWN)
            {
                this.TerminationType = ExecutorTerminationType.FINISHED;
            }
            RunTimer.Stop();
        }

        public void Terminate(bool block=false)
        {
            Console.WriteLine("Terminating early");

            // Technically there is a race here
            // If Run() has not set AllowExecutorToRun to true yet and we set
            // it to false here in another thread then execution can continue anyway.
            AllowExecutorToRun = false;

            // Don't dispose of the solver here. It can lead to races

            if (block)
            {
                Console.WriteLine("Waiting for Executor to finish execution...");
                lock (ExecutorLoopLock)
                {
                    Console.WriteLine("Finished");
                }
            }
        }


        public void TerminateState(ExecutionState state, ITerminationType type, bool removeFromStateScheduler=true)
        {
            state.Terminate(type);
            type.ExitLocation.InstrStatistics.IncrementTerminations(); // Increment the Termination account at the relevant instruction

            if (removeFromStateScheduler)
                StateScheduler.RemoveState(state);

            // Notify
            if (StateTerminated != null)
            {
                StateTerminated(this, new ExecutionStateEventArgs(state));
            }
        }

        protected void ExecuteInstruction()
        {
            Absy currentInstruction = CurrentState.GetCurrentStackFrame().CurrentInstruction.Current;
            if (currentInstruction == null)
                throw new NullReferenceException("Instruction was null");

            // Notify
            if (InstructionVisited != null)
                InstructionVisited(this, new InstructionVisitEventArgs(currentInstruction.GetProgramLocation()));

            #if DEBUG
            // This is heuristic that tries to catch accidental changes to the program
            // by the executor by checking that the string representing the command hasn't changed.
            string original = currentInstruction.ToString();
            #endif

            // FIXME: Use of "dynamic" might hinder performance
            this.Handle(currentInstruction as dynamic);

            ++InternalStatistics.InstructionsExecuted; // Update # of instructions executed

            #if DEBUG
            Debug.Assert(original.Equals( currentInstruction.ToString()), "instruction was changed during execution!");
            #endif
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

            if (v is Constant)
            {
                // This is a special case because we don't normally allow assignment to
                // constants. We make an exception to this rule here
                CurrentState.Mem.Globals[v] = literal;
                return;
            }

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
        protected void EnterImplementation(Implementation Impl, List<Expr> implementationParams)
        {
            bool isProgramEntryPoint = CurrentState.Mem.Stack.Count == 0;

            // FIXME: The boundary between Executor and ExecutionState is
            // unclear, who should do the heavy lifting?
            CurrentState.EnterImplementation(Impl);

            // FIXME: We should check there are no name clashes between
            // existing program variables and symbolics

            // Notify
            if (ImplementationEntered != null)
                ImplementationEntered(this, new EnterImplementationEventArgs(Impl, implementationParams));

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
                if (v.TypedIdent.WhereExpr != null)
                    throw new NotImplementedException("WhereExpr not implemented yet");

                // Make symbolic
                CurrentState.GetCurrentStackFrame().Locals.Add(v, null);
                InitialiseAsSymbolic(v);
            }

            // Record any Globals used in OldExpr for this implementation
            // Or its procedure. It's important we do this before using the MapExecutionStateVariablesDuplicator so
            // it is able to handle any OldExpr
            var oldExprImplGlobals = CurrentState.GetCurrentStackFrame().Impl.GetOldExprVariables();
            if (oldExprImplGlobals.Count > 0)
            {
                foreach (var GV in oldExprImplGlobals)
                {
                    // Note: Duplication of Expr isn't necessary here as we treat Expr immutably
                    CurrentState.GetCurrentStackFrame().OldGlobals[GV] = CurrentState.GetInScopeVariableExpr(GV);
                }
            }

            // Load procedure's requires statements as constraints.
            // We need to rewrite this expression before storing it because it may refer to 
            // procedure arguments rather than the implementation arguments which are confusingly
            // different instances of the same object.
            //
            // We also need to rewrite so that we remove any IdentifierExpr that refer to in program
            // variables and instead replace with expressions containing symbolic variables.
            bool stillInState = true;
            var VR = new MapExecutionStateVariablesDuplicator(CurrentState, this.Builder);
            foreach (var VariablePair in Impl.InParams.Zip(Impl.Proc.InParams))
            {
                // Map Procedure InParams to Implementation InParams
                VR.preReplacementReMap.Add(VariablePair.Item2, VariablePair.Item1);
            }
            foreach (Requires r in Impl.Proc.Requires)
            {
                r.GetInstructionStatistics().IncrementCovered();
                Expr constraint = (Expr) VR.Visit(r.Condition);

                // We need to treat the semantics of requires differently depening on where
                // we are
                if (isProgramEntryPoint)
                {
                    // On entry we treat requires like an assume so it constrains
                    // the initial state
                    stillInState = HandleAssumeLikeCommand(constraint, new TerminatedAtUnsatisfiableEntryRequires(r), r.GetProgramLocation());
                }
                else
                {
                    // We want to treat requires like an assert so that we follow
                    // can follow both potential paths (the assert failing and it succeeding)
                    stillInState = HandleAssertLikeCommand(constraint, new TerminatedAtFailingRequires(r), r.GetProgramLocation());
                }

                ++InternalStatistics.InstructionsExecuted;

                if (!stillInState)
                {
                    // The current state was destroyed so we can't continue handling this command
                    return;
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

                    if (CurrentState.IsInScopeVariable(V) && IsSymbolic(V))
                    {
                        MakeConcrete(V, literal);
                    }
                }
            }
        }

        protected void EnterAndLeaveProcedure(Procedure proc, List<Expr> procedureParams)
        {
            Debug.Assert(CurrentState.Mem.Stack.Count > 0, "Can't enter a procedure without first entering an implementation");
            StackFrame callingStackFrame = CurrentState.GetCurrentStackFrame();

            // Notify
            if (ProcedureEntered != null)
                ProcedureEntered(this, new EnterProcedureEventArgs(proc, procedureParams));

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

            // Record any globals that will be used in OldExpr
            if (proc.GetOldExprVariables().Count > 0)
            {
                foreach (var GV in proc.GetOldExprVariables())
                {
                    // Note: No need to duplicate Expr here as we treat them immutably
                    CurrentState.GetCurrentStackFrame().OldGlobals[GV] = CurrentState.GetInScopeVariableExpr(GV);
                }
            }

            // Assert each requires (this might produce failing states)
            bool stillInState = true;
            var VR = new MapExecutionStateVariablesDuplicator(CurrentState, this.Builder);

            // We don't need to do any of that nasty preReplacementReMap
            // stuff here because there is no implementation
            foreach (var requires in proc.Requires)
            {
                requires.GetInstructionStatistics().IncrementCovered();
                ++InternalStatistics.InstructionsExecuted;
                Expr condition = (Expr) VR.Visit(requires.Condition);

                stillInState = HandleAssertLikeCommand(condition, new TerminatedAtFailingRequires(requires), requires.GetProgramLocation());

                // Check we're still in state
                if (!stillInState)
                {
                    // The CurrentState was terminated so we can't continue
                    return;
                }
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
                ensures.GetInstructionStatistics().IncrementCovered();
                ++InternalStatistics.InstructionsExecuted;
                Expr condition = (Expr) VR.Visit(ensures.Condition);


                // FIXME: We should add an option to disable this because we might want to blindly
                // assume without checking if its feasible.
                stillInState = HandleAssumeLikeCommand(condition, new TerminatedAtUnsatisfiableEnsures(ensures), ensures.GetProgramLocation());

                // Check we're still in state
                if (!stillInState)
                {
                    // The CurrentState was terminated so we can't continue
                    return;
                }
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

            // Notify
            if (ProcedureLeft != null)
                ProcedureLeft(this, new LeaveProcedureEventArgs(proc));

            // Pop the dummy stack
            CurrentState.Mem.PopStackFrame();
        }

        protected void Handle(ReturnCmd c)
        {
            c.GetInstructionStatistics().IncrementCovered();

            var VMR = new MapExecutionStateVariablesDuplicator(CurrentState, this.Builder);

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
                ensures.GetInstructionStatistics().IncrementCovered();
                ++InternalStatistics.InstructionsExecuted;
                Expr remapped = VMR.Visit(ensures.Condition) as Expr;

                // Treat an requires similarly to an assert
                stillInCurrentState = HandleAssertLikeCommand(remapped, new TerminatedAtFailingEnsures(ensures), ensures.GetProgramLocation());

                if (!stillInCurrentState)
                {
                    // The current state was destroyed because an ensures always failed
                    // so we shouldn't try to continue execution of it.
                    return;
                }
            }

            // We presume it is now safe to continue with the return
            Debug.Assert(stillInCurrentState && !this.CurrentState.Finished() , "Cannot do a return if the currentState was terminated!");

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

            // Notify
            if (ImplementationLeft!= null)
                ImplementationLeft(this, new LeaveImplementationEventArgs(CurrentState.GetCurrentStackFrame().Impl));

            // Pop stack frame
            if (CurrentState.Mem.Stack.Count > 1)
                CurrentState.LeaveImplementation();
            else
            {
                // We've finished execution. We deliberately don't pop the stack frame so it can be examined
                TerminateState(CurrentState, new TerminatedWithoutError(c));
            }
        }


        protected void Handle(AssignCmd c)
        {
            c.GetInstructionStatistics().IncrementCovered();

            int index=0;
            var r = new MapExecutionStateVariablesDuplicator(CurrentState, this.Builder);
            Dictionary<Variable, Expr> storedAssignments = new Dictionary<Variable, Expr>();

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

                }
                else
                {
                    throw new NotSupportedException("Unknown type of assignment");
                }

                storedAssignments[lvalue] = rvalue;
                ++index;
            }

            // Now do the assignments safely
            foreach (var assignment in storedAssignments)
            {
                CurrentState.AssignToVariableInScope(assignment.Key, assignment.Value);
            }
        }

        protected void Handle(AssertCmd c)
        {
            c.GetInstructionStatistics().IncrementCovered();

            if (AssertFilter != null)
            {
                if (!AssertFilter(c))
                {
                    // Ignore the assertion
                    return;
                }
            }

            HandleBreakPoints(c);
            var r = new MapExecutionStateVariablesDuplicator(CurrentState, this.Builder);
            var dupAndrw = (Expr) r.Visit(c.Expr);

            // we don't need to care if the current state is destroyed
            HandleAssertLikeCommand(dupAndrw,  new TerminatedAtFailingAssert(c), c.GetProgramLocation());
        }

        protected bool HandleAssertLikeCommand(Expr condition, TerminationTypeWithSatAndUnsatExpr terminatationType, ProgramLocation location)
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
                    terminatationType.ConditionForSat = Expr.True;
                    terminatationType.ConditionForUnsat = Expr.False;
                    TerminateState(CurrentState, terminatationType, /*removeFromStateScheduler=*/true);
                    CurrentState = null;
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
            bool failureIsSpeculative = false;
            bool successIsSpeculative = false;
            switch (result)
            {
                case Solver.Result.SAT:
                    canFail = true;
                    break;
                case Solver.Result.UNKNOWN:
                    Console.WriteLine("Error solver returned UNKNOWN"); // FIXME: Report this to some interface
                    failureIsSpeculative = true;
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
                        successIsSpeculative = true;
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
                if (failureIsSpeculative)
                    CurrentState.MakeSpeculative();

                terminatationType.ConditionForUnsat = condition;
                terminatationType.ConditionForSat = Expr.Not(condition);
                TerminateState(CurrentState, terminatationType, /*removeFromStateScheduler=*/true);
                CurrentState = null;
                return false; // No longer in a state because we removed the current state
            }
            else if (!canFail && canSucceed)
            {
                if (successIsSpeculative)
                    CurrentState.MakeSpeculative();

                // This state can only succeed
                CurrentState.Constraints.AddConstraint(condition, location);
                return true; // We are still in the current state
            }
            else if (canFail && canSucceed)
            {
                // This state can fail and suceed at the current assertion/ensures

                // We need to fork and duplicate the states
                // Or do we? Copying the state just so we can inform
                // the handlers about it seems wasteful...
                ExecutionState failingState = Fork(CurrentState, location);

                if (failureIsSpeculative)
                    failingState.MakeSpeculative();

                // For the failing state we want to state that the negation of the condition
                // is satisfiable (i.e. it can be used to generate a model for the failing execution)
                // terminationType.ConditionForUnsat is not yet because both paths are satisfiable

                // Note: We don't need to duplicate the condition Expr here because we treat them immutably. Clients
                // should be careful to not change this Expr
                terminatationType.ConditionForSat = Builder.Not(condition);
                // The failingState hasn't been added to scheduler so we shouldn't try to remove it from the scheduler
                TerminateState(failingState, terminatationType, /*removeFromStateScheduler=*/false);

                if (successIsSpeculative)
                    CurrentState.MakeSpeculative();

                // successful state can now have assertion expr in constraints
                CurrentState.Constraints.AddConstraint(condition, location);
                return true; // We are still in the current state
            }
            else
            {
                throw new InvalidProgramException("Problem with solver");
            }
        }

        protected bool HandleAssumeLikeCommand(Expr condition, TerminationTypeWithSatAndUnsatExpr terminationType, ProgramLocation location)
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
                    terminationType.ConditionForUnsat = Expr.False;
                    terminationType.ConditionForSat = Expr.True;
                    TerminateState(CurrentState, terminationType, /*removeStateFromScheduler=*/true);
                    CurrentState = null;
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
                    terminationType.ConditionForUnsat = condition;

                    // Expr.Not(condition) will only be satisfiable if
                    // the original constraints are satisfiable
                    // i.e. ¬ ∃ x constraints(x) ∧ query(x) implies that
                    // ∀ x constraints(x) ∧ ¬query(x)
                    // So here we assume
                    terminationType.ConditionForSat = Expr.Not(condition);

                    TerminateState(CurrentState, terminationType, /*removeStateFromScheduler=*/true);
                    CurrentState = null;
                    return false; // No longer in current state

                case Symbooglix.Solver.Result.SAT:
                    CurrentState.Constraints.AddConstraint(condition, location);
                    break;
                case Symbooglix.Solver.Result.UNKNOWN:
                    Console.WriteLine("Solver returned UNKNOWN!"); // FIXME: Report this to an interface.
                    // FIXME: Is this a bug? HandleAssertLikeCmd() assumes that current constraints are satisfiable
                    CurrentState.MakeSpeculative();

                    CurrentState.Constraints.AddConstraint(condition, location);
                    break;
                default:
                    throw new InvalidOperationException("Invalid solver return code");
            }
            return true; // We are still in the current state
        }

        protected void Handle(AssumeCmd c)
        {
            c.GetInstructionStatistics().IncrementCovered();

            HandleBreakPoints(c);
            var r = new MapExecutionStateVariablesDuplicator(CurrentState, this.Builder);
            var dupAndrw = (Expr) r.Visit(c.Expr);

            // Use helper. We don't care if it terminates a state because we immediatly return afterwards
            HandleAssumeLikeCommand(dupAndrw, new TerminatedAtUnsatisfiableAssume(c), c.GetProgramLocation());
        }

        protected void Handle(GotoCmd c)
        {
            Debug.Assert(c.labelTargets.Count() > 0);
            c.GetInstructionStatistics().IncrementCovered();

            if (UseGotoLookAhead)
                LookAheadGotoFork(c);
            else
                SimpleGotoFork(c);
        }

        protected void SimpleGotoFork(GotoCmd c)
        {
            if (c.labelTargets.Count() > 1)
            {
                CurrentState.IncrementExplicitBranchDepth(); // We only increment if there are multiple targets on the goto

                ExecutionState newState = null;
                for (int targetId = 1, tEnd = c.labelTargets.Count; targetId < tEnd; ++targetId)
                {
                    // FIXME: We should look ahead for assumes and check that they are satisfiable so we don't create states and then immediatly destroy them!
                    newState = Fork(CurrentState, c.GetProgramLocation()); // FIXME: This is not memory efficient
                    c.GetInstructionStatistics().IncrementForks();
                    newState.GetCurrentStackFrame().TransferToBlock(c.labelTargets[targetId]);
                    StateScheduler.AddState(newState);

                    // The Current state also needs a new node
                    //CurrentState.TreeNode = new ExecutionTreeNode(CurrentState, CurrentState.TreeNode, c.GetProgramLocation());
                }
            }

            // The current execution state will always take the first target
            CurrentState.GetCurrentStackFrame().TransferToBlock(c.labelTargets[0]);
        }

        private struct LookAheadInfo
        {
            public Expr ReWrittenAssumeExpr; // null if no assume to look ahead
            public Block Target;
            public bool IsSpeculative;
        }

        protected void LookAheadGotoFork(GotoCmd c)
        {

            var blocksToExecute = new List<LookAheadInfo>();

            // After running over label targets this list will
            // contain the targets that will be followed.
            // If Expr is null it means that an assume was
            // not found as the first instruction at the target
            // so it should be executed normally.
            // If the Expr is not null then it is the rewritten expression
            // from an assume instruction that should be added to the constraints
            var remapper = new MapExecutionStateVariablesDuplicator(CurrentState, this.Builder);
            foreach (var block in c.labelTargets)
            {
                LookAheadInfo info;
                info.IsSpeculative = false;
                info.ReWrittenAssumeExpr = null;
                info.Target = block;

                var targetInstruction = new BlockCmdEnumerator(block);
                targetInstruction.MoveNext();

                if (!( targetInstruction.Current is AssumeCmd ))
                {
                    // There is no assume cmd at the beginning of the target block
                    // so this will need to be executed.
                    blocksToExecute.Add(info);
                    continue;
                }

                var assumeCmd = targetInstruction.Current as AssumeCmd;

                Expr dupAndRw = (Expr) remapper.Visit(assumeCmd.Expr);


                info.ReWrittenAssumeExpr = dupAndRw;

                // Fast path
                if (dupAndRw is LiteralExpr)
                {
                    var lit = dupAndRw as LiteralExpr;
                    Debug.Assert(lit.isBool, "Expression should be boolean");

                    if (lit.asBool)
                    {
                        blocksToExecute.Add(info);
                    }
                    else
                    {
                        // Infeasible path so don't add to blocksToExecute
                    }
                }
                else
                {
                    // Ask to solver if the assume is satisfiable
                    TheSolver.SetConstraints(CurrentState.Constraints);
                    Solver.Result result = TheSolver.IsQuerySat(dupAndRw);
                    switch (result)
                    {
                        case Symbooglix.Solver.Result.UNKNOWN:
                            info.IsSpeculative = true;
                            blocksToExecute.Add(info);
                            break;
                        case Symbooglix.Solver.Result.SAT:
                            blocksToExecute.Add(info);
                            break;
                        case Symbooglix.Solver.Result.UNSAT:
                        // Following this path would lead to in an infeasiable execution state
                        // so drop it don't add it to blocksToExecute
                            break;
                        default:
                            throw new NotImplementedException("Unhandled case");
                    }
                }
            }

            // Now create the ExecutionStates that we know will be feasible

            if (blocksToExecute.Count == 0)
            {
                // No paths are feasible so terminate current state
                // FIXME: Need new termination type
                TerminateState(CurrentState, new TerminatedAtGotoWithUnsatisfiableTargets(c), /*removeFromStateSchedular=*/ true);
                return;
            }

            // Will contain the execution states we want
            var forkingStates = new List<ExecutionState>();
            forkingStates.Add(CurrentState);

            if (c.labelTargets.Count > 1)
            {
                // We only increment the branch depth if there is more than
                // one target to follow. It is important that we do this before
                // we fork from CurrentState so that the branch depth is inherited
                // and in Fork() the creation of the ExecutionTreeNode has the correct
                // depth.
                // FIXME: Can we make this less fragile?
                CurrentState.IncrementExplicitBranchDepth();
            }

            // Create new ExecutionStates for the other blocks
            for (int index = 1; index < blocksToExecute.Count; ++index)
            {
                var newState = Fork(CurrentState, c.GetProgramLocation());
                c.GetInstructionStatistics().IncrementForks();
                forkingStates.Add(newState);
            }

            // Finally Setup each ExecutionState as appropriate and set it up to follow the appropriate path
            Debug.Assert(forkingStates.Count == blocksToExecute.Count, "Created wrong number of states to Execute");
            foreach (var blockStatePair in blocksToExecute.Zip(forkingStates))
            {
                var theState = blockStatePair.Item2;
                var theInfo = blockStatePair.Item1;

                if (theInfo.IsSpeculative)
                {
                    theState.MakeSpeculative();
                }

                // Transfer to the appropriate basic block
                theState.GetCurrentStackFrame().TransferToBlock(theInfo.Target);

                if (theInfo.ReWrittenAssumeExpr != null)
                {
                    // For this state we looked ahead and there was a satisfiable assume
                    // so now add the assume constraint and walk past the assume that we
                    // already looked at because there is no need to execute it.
                    var assumeCmd = (theInfo.Target.Cmds[0] as AssumeCmd);
                    Debug.Assert(assumeCmd != null, "The target block does not start with the expected AssumeCmd");
                    theState.Constraints.AddConstraint(theInfo.ReWrittenAssumeExpr, assumeCmd.GetProgramLocation());

                    // We only increment the coverage on paths that we actually follow
                    assumeCmd.GetInstructionStatistics().IncrementCovered();

                    // Move the currentInstruction to point to the AssumeCmd.
                    // When the Executor loop execute's "theState"'s next instruction
                    // it will move forward again thus skipping the AssumeCmd
                    theState.GetCurrentStackFrame().CurrentInstruction.MoveNext();
                    Debug.Assert(theState.GetCurrentStackFrame().CurrentInstruction.Current is AssumeCmd, "The target block does not start with the expected AssumeCmd");
                }

                // Add the new states to the scheduler
                if (theState != CurrentState)
                    StateScheduler.AddState(theState);
            }

            if (c.labelTargets.Count > 1)
            {
                // We need to make a new ExecutionTree node for the CurrentState because it has gone deeper
                //CurrentState.TreeNode = new ExecutionTreeNode(CurrentState, CurrentState.TreeNode, c.GetProgramLocation());
            }
        }

        protected void Handle(CallCmd c)
        {
            c.GetInstructionStatistics().IncrementCovered();

            var args = new List<Expr>();
            var reWritter = new MapExecutionStateVariablesDuplicator(CurrentState, this.Builder);

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
                var arg = (Expr) reWritter.Visit(e);
                args.Add( arg );
            }


            if (impl != null)
            {
                EnterImplementation(impl, args);
            }
            else
            {
                EnterAndLeaveProcedure(c.Proc, args);
            }
        }

        protected void Handle(HavocCmd c)
        {
            c.GetInstructionStatistics().IncrementCovered();

            for (int index=0; index < c.Vars.Count ; ++index)
            {
                var s = SymbolicPool.getFreshSymbolic(c, index);
                Debug.Assert(CurrentState.IsInScopeVariable(c.Vars[index]), "Havoc variable is not in scope");
                CurrentState.AssignToVariableInScope(c.Vars[index].Decl, s.Expr);
                CurrentState.Symbolics.Add(s);

            }
        }

        protected void Handle(YieldCmd c)
        {
            c.GetInstructionStatistics().IncrementCovered();
            throw new NotImplementedException ();
        }

        protected ExecutionState Fork(ExecutionState stateToFork, ProgramLocation createdAt)
        {
            var newState = stateToFork.DeepClone();

            // Should DeepClone() handle this instead?
            //newState.TreeNode = new ExecutionTreeNode(newState, stateToFork.TreeNode, createdAt);
            ++InternalStatistics.ForkCount;
            return newState;
        }

    }
}

