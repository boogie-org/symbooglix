//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using BPLType = Microsoft.Boogie.Type;

namespace Symbooglix
{

    public class Executor : Util.IYAMLWriter
    {
        public Executor(Program program, IStateScheduler scheduler, Solver.ISolver solver, IExprBuilder builder, ISymbolicPool symbolicPool)
        { 
            this.TheProgram = program;
            StateScheduler = scheduler;
            SymbolicPool = symbolicPool;
            UseGotoLookAhead = true;
            UseGlobalDDE = true;
            UseForkAtPredicatedAssign = false;
            CheckEntryAxioms = true;
            CheckEntryRequires = true;
            CheckUniqueVariableDecls = true;
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

            if (!builder.Immutable)
                throw new ArgumentException("builder must build immutable expressions");
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
        private ISymbolicPool SymbolicPool;
        public bool HasBeenPrepared
        {
            get;
            private set;
        }
        public Solver.ISolver TheSolver;
        private bool AllowExecutorToRun= false;
        public Predicate<AssertCmd> AssertFilter
        {
            get;
            set;
        }

        // FIXME: This API is lame make them constructor parameters
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

        public bool UseForkAtPredicatedAssign
        {
            get;
            set;
        }

        public bool CheckEntryAxioms
        {
            get;
            set;
        }

        public bool CheckEntryRequires
        {
            get;
            set;
        }

        public bool CheckUniqueVariableDecls
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
            INITIAL_STATE_TERMINATED,
            FINISHED,
            TIMEOUT,
            OUT_OF_MEMORY,
            TERMINATE_CALLED,
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

        public class ForkEventArgs : EventArgs
        {
            public ExecutionState Parent { get; private set; }
            public ExecutionState Child { get; private set; }
            public ForkEventArgs(ExecutionState parent , ExecutionState child)
            {
                this.Parent = parent;
                this.Child = child;
            }
        }
        public event EventHandler<ForkEventArgs> ForkOccurred;

        public class TransferToBlockEventArgs : EventArgs
        {
            public ExecutionState State { get; private set; }
            public Block PreviousBlock { get; private set; }
            public Block NewBlock { get; private set; }
            public TransferToBlockEventArgs(ExecutionState state, Block previousBlock, Block newBlock)
            {
                State = state;
                PreviousBlock = previousBlock;
                NewBlock = newBlock;
            }
        }

        public event EventHandler<TransferToBlockEventArgs> BasicBlockChanged;

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

            // Line coverage
            var lineCoverage = TheProgram.GetLineCoverage();
            TW.WriteLine("lines_covered: {0} # ({1}%)", lineCoverage.CoveredLines, 100*(( (double) lineCoverage.CoveredLines)/lineCoverage.TotalLines));
            TW.WriteLine("total_lines: {0}", lineCoverage.TotalLines);

            TW.WriteLine("symbolic_pool:");
            TW.Indent += 1;
            SymbolicPool.WriteAsYAML(TW);
            TW.Indent -= 1;

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

            //This is a workaround to the issue described at https://github.com/boogie-org/boogie/issues/92.
            InternalPreparationPassManager.Add(new Transform.PruneUnreachableBlocksPass());

            if (UseGlobalDDE)
                InternalPreparationPassManager.Add(new Transform.GlobalDeadDeclEliminationPass());

            InternalPreparationPassManager.Add(new Transform.OldExprCanonicaliser());

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
                var s = SymbolicPool.GetFreshSymbolic(gv, CurrentState);
                Debug.Assert(!InitialState.Mem.Globals.ContainsKey(gv), "Cannot insert global that is already in memory");
                InitialState.Mem.Globals.Add(gv, s.Expr);

                var gvAsConstant = gv as Constant;
                if (gvAsConstant != null)
                {
                    if (gvAsConstant.ChildrenComplete)
                        throw new NotSupportedException("complete keyword not supported");

                    if (gvAsConstant.Parents != null)
                        throw new NotSupportedException("extends keyword not supported");
                }

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
                var VMR = new MapExecutionStateVariablesDuplicator(InitialState, this.Builder);
                VMR.ReplaceGlobalsOnly = true; // The stackframe doesn't exist yet!

                Expr axiomVMRExpr = (Expr) VMR.Visit(axiom.Expr);
                var constraint = new Constraint(axiomVMRExpr, axiom.GetProgramLocation());

                if (CheckEntryAxioms)
                {
                    var query = new Solver.Query(InitialState.Constraints, constraint);
                    var result = TheSolver.CheckSatisfiability(query);
                    switch (result.Satisfiability)
                    {
                        case Symbooglix.Solver.Result.SAT:
                            break;
                        case Symbooglix.Solver.Result.UNSAT:
                            goto default;
                        case Symbooglix.Solver.Result.UNKNOWN:
                            InitialState.MakeSpeculative(axiom.GetProgramLocation());
                            goto default; // Eurgh...
                        default:
                            var terminatedAtUnsatisfiableAxiom = new TerminatedAtUnsatisfiableAxiom(axiom);
                            terminatedAtUnsatisfiableAxiom.ConditionForUnsat = axiomVMRExpr;

                        // Builder.Not(constraint) will only be satisfiable if
                        // the original constraints are satisfiable
                        // i.e. ¬ ∃ x constraints(x) ∧ query(x) implies that
                        // ∀ x constraints(x) ∧ ¬query(x)
                        // So here we assume
                            terminatedAtUnsatisfiableAxiom.ConditionForSat = Builder.Not(axiomVMRExpr);

                            TerminateState(InitialState, terminatedAtUnsatisfiableAxiom, /*removeFromStateScheduler=*/false);
                            HasBeenPrepared = true; // Don't allow this method to run again
                            PrepareTimer.Stop();
                            return false;
                    }
                }
                else
                {
                    // FIXME: Emit as event
                    Console.Error.WriteLine("Warning: Not checking axiom {0}:{1} {2}", axiom.tok.filename, axiom.tok.line, axiom.Expr);
                }

                InitialState.Constraints.AddConstraint(constraint);
                Debug.WriteLine("Adding constraint : " + axiomVMRExpr);

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

            // Enforce "unique" keyword
            var groupedVariables = TheProgram.TopLevelDeclarations.OfType<Constant>().Where( c => c.Unique).GroupBy( c => c.TypedIdent.Type);
            foreach (var grouping in groupedVariables)
            {
                var varsToEnforceUnique = grouping.ToList();

                var exprToEnforceUnique = new List<Expr>();
                foreach (var constantVar in varsToEnforceUnique)
                {
                    exprToEnforceUnique.Add(InitialState.Mem.Globals[constantVar]);
                }

                // HACK: There are multiple program locations associated with the enforcement of a distinct Expr
                var progLoc = varsToEnforceUnique[0].GetProgramLocation();
                var distinctExpr = Builder.Distinct(exprToEnforceUnique);
                var distinctConstraint = new Constraint(distinctExpr, progLoc);
                if (CheckUniqueVariableDecls)
                {
                    // Check the constraint is satisfiable
                    var query = new Solver.Query(InitialState.Constraints, distinctConstraint);
                    var result = TheSolver.CheckSatisfiability(query);
                    switch (result.Satisfiability)
                    {
                        case Symbooglix.Solver.Result.SAT:
                            break;
                        case Symbooglix.Solver.Result.UNSAT:
                            goto default;
                        case Symbooglix.Solver.Result.UNKNOWN:

                            InitialState.MakeSpeculative(progLoc);
                            goto default; // Eurgh...
                        default:
                            var terminatedWithUnsatUniqueAttr = new TerminatedWithUnsatisfiableUniqueAttribute(varsToEnforceUnique);
                            terminatedWithUnsatUniqueAttr.ConditionForUnsat = distinctExpr;

                        // Builder.Not(constraint) will only be satisfiable if
                        // the original constraints are satisfiable
                        // i.e. ¬ ∃ x constraints(x) ∧ query(x) implies that
                        // ∀ x constraints(x) ∧ ¬query(x)
                        // So here we assume
                            terminatedWithUnsatUniqueAttr.ConditionForSat = Builder.Not(distinctExpr);

                            TerminateState(InitialState, terminatedWithUnsatUniqueAttr, /*removeFromStateScheduler=*/false);
                            HasBeenPrepared = true; // Don't allow this method to run again
                            PrepareTimer.Stop();
                            return false;
                    }
                }
                else
                {
                    // FIXME: Emit as some sort of event
                    Console.WriteLine("WARNING: Not checking if the uniqueness of variables of type {0} is satisfiable",
                                      varsToEnforceUnique[0].TypedIdent.Type.ToString());
                }
                InitialState.Constraints.AddConstraint(distinctConstraint);
                Debug.WriteLine("Adding constraint : " + distinctExpr);
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

            var theTerminationType = ExecutorTerminationType.TIMEOUT;
            // Create a thread that will kill the executor after the timeout is hit.
            Task.Factory.StartNew(() =>
            {
                Thread.Sleep(timeout * 1000); // argument is in milliseconds
                this.TerminationType = theTerminationType;
                // Notify
                if (ExecutorTimeoutReached != null)
                {
                    var eventArg = new ExecutorTimeoutReachedArgs();
                    ExecutorTimeoutReached(this, eventArg );
                }

                // Use internalTerminate so the terminationType does not get overwritten
                this.InternalTerminate(/*block=*/ false, /*interruptSolver=*/ true, theTerminationType);
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
                Exception otherException = null;
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
                catch (Exception e)
                {
                    otherException = e;
                    throw;
                }
                finally
                {
                    // HACK: If another type of exception, exit early so we don't
                    // try to notify of Executor termination which might raise more
                    // exceptions obscuring the original
                    if (otherException == null)
                    {
                        // Console.WriteLine("Notifying listeners of Executor termination");
                        // Notify listeners that the Executor finished.

                        // If we ran out of memory the hope is that we free'd enough
                        // for the listeners to be able to complete but this is not guaranteed.
                        if (ExecutorTerminated != null)
                        {
                            ExecutorTerminated(this, new ExecutorTerminatedArgs(this));
                        }
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
                this.TerminationType = ExecutorTerminationType.INITIAL_STATE_TERMINATED;

                if (ExecutorTerminated != null)
                    ExecutorTerminated(this, new ExecutorTerminatedArgs(this));

                throw new InitialStateTerminated(this, InitialState);
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
                    this.TerminateState(CurrentState, new TerminatedWithDisallowedSpeculativePath(CurrentState.SpeculativeStart));
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

        public void Terminate(bool block=false, bool interruptSolver=true)
        {
            InternalTerminate(block, interruptSolver, ExecutorTerminationType.TERMINATE_CALLED);
        }

        private void InternalTerminate(bool block, bool interruptSolver, ExecutorTerminationType terminationType)
        {
            this.TerminationType = terminationType;
            Console.WriteLine("Terminating Executor early with reason {0}", this.TerminationType);

            // Technically there is a race here
            // If Run() has not set AllowExecutorToRun to true yet and we set
            // it to false here in another thread then execution can continue anyway.
            AllowExecutorToRun = false;

            if (interruptSolver)
                TheSolver.Interrupt();

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

            // Constant variables don't have InstrStatistics so don't try to increment them
            if (!(type is TerminatedWithUnsatisfiableUniqueAttribute))
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

        protected SymbolicVariable InitialiseLocalAsSymbolic(Variable v)
        {
            var s = SymbolicPool.GetFreshSymbolic(v, CurrentState);
            CurrentState.GetCurrentStackFrame().Locals.Add(v, s.Expr);
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
                    InitialiseLocalAsSymbolic(v);
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
                InitialiseLocalAsSymbolic(v);
            }

            // Load procedure's declared locals on to stack
            foreach(Variable v in Impl.LocVars)
            {
                if (v.TypedIdent.WhereExpr != null)
                    throw new NotImplementedException("WhereExpr not implemented yet");

                // Make symbolic
                InitialiseLocalAsSymbolic(v);
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
                    if (CheckEntryRequires)
                    {
                        stillInState = HandleAssumeLikeCommand(constraint, new TerminatedAtUnsatisfiableEntryRequires(r), r.GetProgramLocation());
                    }
                    else
                    {
                        // FIXME: Emit as event
                        Console.Error.WriteLine("Warning: Not checking entry constraint {0}:{1} {2}", r.tok.filename, r.tok.line, r.Condition);
                        CurrentState.Constraints.AddConstraint(constraint, r.GetProgramLocation());
                    }
                }
                else
                {
                    // We want to treat requires like an assert so that we follow
                    // can follow both potential paths (the assert failing and it succeeding)
                    stillInState = HandleAssertLikeCommand(constraint, new TerminatedAtFailingRequires(r), r.GetProgramLocation());
                }

                ++InternalStatistics.InstructionsExecuted;

                if (!stillInState || !AllowExecutorToRun)
                {
                    // The current state was destroyed or the executor has been asked to terminated
                    // so we can't continue handling this command
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
                    Debug.Assert(literal != null, "Literal assignment cannot be null");
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

                    if (V is GlobalVariable)
                    {
                        // Also concretise stored old expressions
                        if (oldExprImplGlobals.Contains(V))
                        {
                            CurrentState.GetCurrentStackFrame().OldGlobals[V as GlobalVariable] = literal;
                        }
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
                InitialiseLocalAsSymbolic(v);
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

                // Check we're still in state and allowed to run
                if (!stillInState || !AllowExecutorToRun)
                {
                    // The CurrentState was terminated so we can't continue
                    return;
                }
            }

            // Make the Global variables in Modset Symbolic
            for (int modSetIndex=0;  modSetIndex < proc.Modifies.Count ; ++modSetIndex)
            {
                var symbolic = SymbolicPool.GetFreshSymbolic(proc, modSetIndex, CurrentState);
                CurrentState.AssignToVariableInScope(proc.Modifies[modSetIndex].Decl, symbolic.Expr);
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
                if (!stillInState || !AllowExecutorToRun)
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

                if (!stillInCurrentState || !AllowExecutorToRun)
                {
                    // The current state was destroyed because an ensures always failed
                    // or the executor was asked to halt
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

        // FIXME: Add unit tests for this
        protected void HandlePredicatedAssign(AssignCmd assignCmd, Variable v, NAryExpr ite)
        {
            Debug.Assert(ExprUtil.AsIfThenElse(ite) != null);
            Expr condition = ite.Args[0];
            Expr thenExpr = ite.Args[1];
            Expr elseExpr = ite.Args[2];
            Debug.Assert(condition.Immutable);
            Debug.Assert(thenExpr.Immutable);
            Debug.Assert(elseExpr.Immutable);

            var constraint = new Constraint(condition, assignCmd.GetProgramLocation());
            var result = TheSolver.CheckBranchSatisfiability(CurrentState.Constraints, constraint, this.Builder);

            bool canFollowElse = (result.FalseBranch != Solver.Result.UNSAT);
            bool canFollowThen = (result.TrueBranch != Solver.Result.UNSAT);
            bool followingElseIsSpeculative = (result.FalseBranch == Solver.Result.UNKNOWN);
            bool followThenIsSpeculative = (result.TrueBranch == Solver.Result.UNKNOWN);


            if (canFollowElse && !canFollowThen)
            {
                if (followingElseIsSpeculative)
                    CurrentState.MakeSpeculative(assignCmd.GetProgramLocation());

                // The elseExpr will be used, because this a predicated assignment
                // and the value is the current state won't be changed
                Debug.Assert(CurrentState.GetInScopeVariableExpr(v).Equals(elseExpr), "elseExpr should just be the variable being assigned to");
                CurrentState.Constraints.AddConstraint(constraint.GetNegatedConstraint(this.Builder));

            }
            else if (!canFollowElse && canFollowThen)
            {
                if (followThenIsSpeculative)
                    CurrentState.MakeSpeculative(assignCmd.GetProgramLocation());

                // Only the thenExpr will be used so perform assignment
                CurrentState.AssignToVariableInScope(v, thenExpr);
                CurrentState.Constraints.AddConstraint(constraint);
            }
            else if (canFollowElse && canFollowThen)
            {
                // This state can follow elseExpr and follow thenExpr at the assign
                ExecutionState elseState = Fork(CurrentState, assignCmd.GetProgramLocation());

                if (followingElseIsSpeculative)
                    elseState.MakeSpeculative(assignCmd.GetProgramLocation());

                // The elseExpr will be used, because this a predicated assignment
                // and the value is the current state won't be changed
                Debug.Assert(elseState.GetInScopeVariableExpr(v).Equals(elseExpr), "elseExpr should just be the variable being assigned to");
                elseState.Constraints.AddConstraint(constraint.GetNegatedConstraint(this.Builder));
                StateScheduler.AddState(elseState);


                if (followThenIsSpeculative)
                    CurrentState.MakeSpeculative(assignCmd.GetProgramLocation());

                // thenExpr used
                CurrentState.AssignToVariableInScope(v, thenExpr);

                // successful state can now have assertion expr in constraints
                CurrentState.Constraints.AddConstraint(constraint);
            }
            else
            {
                // FIXME: Use a proper exception
                throw new InvalidProgramException("Solver error");
            }
        }


        protected void Handle(AssignCmd c)
        {
            c.GetInstructionStatistics().IncrementCovered();
            var r = new MapExecutionStateVariablesDuplicator(CurrentState, this.Builder);

            // Handle predicated assignment to prevent Expr blow-up
            // in loops
            if (UseForkAtPredicatedAssign && c.Lhss.Count == 1)
            {
                Variable lhs = c.Lhss[0].DeepAssignedVariable;
                Expr rhs = c.Rhss[0];
                var ite = ExprUtil.AsIfThenElse(rhs);
                if (ite != null)
                {
                    var elseExpr = ite.Args[2];
                    var id = ExprUtil.AsIdentifer(elseExpr);
                    if (id != null)
                    {
                        if (id.Decl.Equals(lhs))
                        {
                            Expr expandedIte = null;
                            if (c.Lhss[0] is SimpleAssignLhs)
                            {
                                // Duplicate and Expand out the expression so we only have symbolic identifiers in the expression
                                expandedIte = (Expr) r.Visit(ite);
                            }
                            else if (c.Lhss[0] is MapAssignLhs)
                            {
                                // We need to use "AsSimleAssignCmd" so that we have a single Variable as lhs and MapStore expressions
                                // on the right hand side
                                var ac = c.AsSimpleAssignCmd;
                                expandedIte = ac.Rhss[0];
                                // Duplicate and Expand out the expression so we only have symbolic identifiers in the expression
                                expandedIte = (Expr) r.Visit(expandedIte);
                            }
                            else
                            {
                                throw new NotSupportedException("AssignLHS not supported");
                            }

                            // After constant folding, we might not have an ITE anymore
                            if (ExprUtil.AsIfThenElse(expandedIte) != null)
                            {
                                HandlePredicatedAssign(c, lhs, expandedIte as NAryExpr);
                                return;
                            }
                        }
                    }
                }
            }

            int index=0;
            Dictionary<Variable, Expr> storedExprAssignments = new Dictionary<Variable, Expr>();
            Dictionary<Variable, Tuple<List<Expr>, Expr>> directMapAssignment = new Dictionary<Variable, Tuple<List<Expr>, Expr>>();
            Dictionary<Variable, Variable> directMapCopies = new Dictionary<Variable, Variable>();

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

                bool didExpressionAssign = true;
                if (lhsrhs.Item1 is SimpleAssignLhs)
                {
                    if (lhsrhs.Item1.DeepAssignedVariable.TypedIdent.Type.IsMap && ExprUtil.AsIdentifer(lhsrhs.Item2) != null)
                    {
                        // This is a direct map copy
                        var destVar = lhsrhs.Item1.DeepAssignedVariable;
                        var srcVar = ExprUtil.AsIdentifer(lhsrhs.Item2).Decl;
                        Debug.Assert(destVar.TypedIdent.Type.Equals(srcVar.TypedIdent.Type));
                        directMapCopies.Add(destVar, srcVar);
                        didExpressionAssign = false;
                    }
                    else
                    {
                        // Direct expression assignment

                        // Duplicate and Expand out the expression so we only have symbolic identifiers in the expression
                        rvalue = (Expr) r.Visit(lhsrhs.Item2);
                        didExpressionAssign = true;
                    }
                }
                else if (lhsrhs.Item1 is MapAssignLhs)
                {
                    var indicies = ComputeMapAssignIndices(lhsrhs.Item1 as MapAssignLhs);

                    if (indicies != null)
                    {
                        // Doing direct assignment to map using indicies
                        rvalue = (Expr) r.Visit(lhsrhs.Item2);

                        // Need to do replacement in the indicies
                        var dupAndRIndices = new List<Expr>();
                        foreach (var mapIndex in indicies)
                        {
                            dupAndRIndices.Add((Expr) r.Visit(mapIndex));
                        }

                        directMapAssignment.Add(lvalue, Tuple.Create(dupAndRIndices, rvalue));
                        didExpressionAssign = false;
                    }
                    else
                    {
                        // The map isn't being fully indexed into so compute the necessary mapstores and selects to directly assign to the variable

                        // We need to use "AsSimleAssignCmd" so that we have a single Variable as lhs and MapStore expressions
                        // on the right hand side
                        var ac = c.AsSimpleAssignCmd;
                        Debug.Assert(ac.Lhss[index].DeepAssignedVariable == lvalue, "lvalue mismatch");
                        rvalue = ac.Rhss[index];
                        // Duplicate and Expand out the expression so we only have symbolic identifiers in the expression
                        rvalue = (Expr) r.Visit(rvalue);
                        didExpressionAssign = true;
                    }

                }
                else
                {
                    throw new NotSupportedException("Unknown type of assignment");
                }

                if (didExpressionAssign)
                {
                    storedExprAssignments[lvalue] = rvalue;
                }
                ++index;
            }

            // The semantics of parallel map assign mean that we shouldn't do any writes until we've read
            // everything

            // Now do the assignments safely
            foreach (var assignment in storedExprAssignments)
            {
                CurrentState.AssignToVariableInScope(assignment.Key, assignment.Value);
            }

            // Now do direct map assignments safely
            foreach (var mapAssignment in directMapAssignment)
            {
                CurrentState.AssignToMapVariableInScopeAt(mapAssignment.Key, mapAssignment.Value.Item1, mapAssignment.Value.Item2);
            }

            // Now do map copies safely
            foreach (var pair in directMapCopies)
            {
                CurrentState.DirectMapCopy(pair.Key, pair.Value);
            }
        }

        // Returns null if it not a direct assignment
        private List<Expr> ComputeMapAssignIndices(MapAssignLhs malhs)
        {
            // We will traverse the assignment building up the indices. The indices
            // are actually backwards so we will need reverse at the end.
            AssignLhs currentAssign = malhs;
            var indices = new List<Expr>();
            do
            {
                var asMapAssign = currentAssign as MapAssignLhs;
                // Add the indices at this assign backwards so what when we reverse
                // later they will be the correct way round.
                foreach (var index in asMapAssign.Indexes.AsEnumerable().Reverse())
                {
                    indices.Add(index);
                }
                currentAssign = asMapAssign.Map;
            } while (currentAssign is MapAssignLhs);

            // traverse type to check indices length match. We might only be partially assigning into the map
            // Precompute the number of indicies required to perform a read or write
            int numberOfIndices = 0;
            BPLType mapCodomainTy = malhs.DeepAssignedVariable.TypedIdent.Type.AsMap; // Initially not the codmain
            do
            {
                Debug.Assert(mapCodomainTy is MapType);
                var asMap = mapCodomainTy.AsMap;
                numberOfIndices += asMap.Arguments.Count;
                mapCodomainTy = asMap.Result;
            } while (mapCodomainTy.IsMap);

            if (numberOfIndices != indices.Count)
                return null; // The assignment doesn't index all the way through the nested maps

            // We do index all the
            // Put the indices in the write order
            indices.Reverse();
            return indices;
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
            var trueBranchConstraint = new Constraint(condition, location);
            var result = TheSolver.CheckBranchSatisfiability(CurrentState.Constraints, trueBranchConstraint, this.Builder);

            bool canFail = (result.FalseBranch != Solver.Result.UNSAT);
            bool canSucceed = (result.TrueBranch != Solver.Result.UNSAT);
            bool failureIsSpeculative = (result.FalseBranch == Solver.Result.UNKNOWN);
            bool successIsSpeculative = ( result.TrueBranch == Solver.Result.UNKNOWN);


            if (canFail && !canSucceed)
            {
                Debug.Assert(result.TrueBranch == Solver.Result.UNSAT);
                Debug.Assert(result.FalseBranch == Solver.Result.SAT || result.FalseBranch == Solver.Result.UNKNOWN);

                if (failureIsSpeculative)
                    CurrentState.MakeSpeculative(location);

                terminatationType.ConditionForUnsat = condition;
                terminatationType.ConditionForSat = Builder.Not(condition);
                TerminateState(CurrentState, terminatationType, /*removeFromStateScheduler=*/true);
                CurrentState = null;
                return false; // No longer in a state because we removed the current state
            }
            else if (!canFail && canSucceed)
            {
                Debug.Assert(result.TrueBranch == Solver.Result.SAT || result.TrueBranch == Solver.Result.UNKNOWN);
                Debug.Assert(result.FalseBranch == Solver.Result.UNSAT);

                if (successIsSpeculative)
                    CurrentState.MakeSpeculative(location);

                // This state can only succeed
                CurrentState.Constraints.AddConstraint(trueBranchConstraint);
                return true; // We are still in the current state
            }
            else if (canFail && canSucceed)
            {
                Debug.Assert(result.TrueBranch == Solver.Result.SAT || result.TrueBranch == Solver.Result.UNKNOWN);
                Debug.Assert(result.FalseBranch == Solver.Result.SAT || result.FalseBranch == Solver.Result.UNKNOWN);

                // This state can fail and suceed at the current assertion/ensures

                // We need to fork and duplicate the states
                // Or do we? Copying the state just so we can inform
                // the handlers about it seems wasteful...
                ExecutionState failingState = Fork(CurrentState, location);

                if (failureIsSpeculative)
                    failingState.MakeSpeculative(location);

                // For the failing state we want to state that the negation of the condition
                // is satisfiable (i.e. it can be used to generate a model for the failing execution)
                // terminationType.ConditionForUnsat is not yet because both paths are satisfiable

                // Note: We don't need to duplicate the condition Expr here because we treat them immutably. Clients
                // should be careful to not change this Expr
                terminatationType.ConditionForSat = Builder.Not(condition);
                // The failingState hasn't been added to scheduler so we shouldn't try to remove it from the scheduler
                TerminateState(failingState, terminatationType, /*removeFromStateScheduler=*/false);

                if (successIsSpeculative)
                    CurrentState.MakeSpeculative(location);

                // successful state can now have assertion expr in constraints
                CurrentState.Constraints.AddConstraint(trueBranchConstraint);
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
            var constraint = new Constraint(condition, location);
            var result = TheSolver.CheckSatisfiability(new Solver.Query(CurrentState.Constraints, constraint));
            switch (result.Satisfiability)
            {
                case Symbooglix.Solver.Result.UNSAT:
                    terminationType.ConditionForUnsat = condition;

                    // Builder.Not(condition) will only be satisfiable if
                    // the original constraints are satisfiable
                    // i.e. ¬ ∃ x constraints(x) ∧ query(x) implies that
                    // ∀ x constraints(x) → ¬query(x)
                    // So here we assume
                    terminationType.ConditionForSat = Builder.Not(condition);

                    TerminateState(CurrentState, terminationType, /*removeStateFromScheduler=*/true);
                    CurrentState = null;
                    return false; // No longer in current state

                case Symbooglix.Solver.Result.SAT:
                    CurrentState.Constraints.AddConstraint(constraint);
                    break;
                case Symbooglix.Solver.Result.UNKNOWN:
                    Console.WriteLine("Solver returned UNKNOWN!"); // FIXME: Report this to an interface.
                    // FIXME: Is this a bug? HandleAssertLikeCmd() assumes that current constraints are satisfiable
                    CurrentState.MakeSpeculative(location);

                    CurrentState.Constraints.AddConstraint(constraint);
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
                    TransferStateToBlock(newState, c.labelTargets[targetId]);
                    StateScheduler.AddState(newState);

                    // The Current state also needs a new node
                    //CurrentState.TreeNode = new ExecutionTreeNode(CurrentState, CurrentState.TreeNode, c.GetProgramLocation());
                }
            }

            // The current execution state will always take the first target
            TransferStateToBlock(CurrentState, c.labelTargets[0]);
        }

        private struct LookAheadInfo
        {
            public Constraint ReWrittenAssumeConstraint; // null if no assume to look ahead
            public Block Target;
            public bool IsSpeculative;
            public AssumeCmd Assume; // null if no assume to look ahead
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
                info.ReWrittenAssumeConstraint = null;
                info.Target = block;
                info.Assume = null;

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
                info.Assume = assumeCmd;

                Expr dupAndRw = (Expr) remapper.Visit(assumeCmd.Expr);


                info.ReWrittenAssumeConstraint = new Constraint(dupAndRw, assumeCmd.GetProgramLocation());

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
                    if (!AllowExecutorToRun)
                    {
                        // Prevent anymore calls to the solver if we were asked
                        // to terminate. This can leave the current ExecutionState
                        // in an undefined state.
                        return;
                    }

                    // Ask to solver if the assume is satisfiable
                    var result = TheSolver.CheckSatisfiability(new Solver.Query(CurrentState.Constraints, info.ReWrittenAssumeConstraint));
                    switch (result.Satisfiability)
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
                    Debug.Assert(theInfo.Assume != null);
                    theState.MakeSpeculative(theInfo.Assume.GetProgramLocation());
                }

                // Transfer to the appropriate basic block
                TransferStateToBlock(theState, theInfo.Target);

                if (theInfo.ReWrittenAssumeConstraint != null)
                {
                    // For this state we looked ahead and there was a satisfiable assume
                    // so now add the assume constraint and walk past the assume that we
                    // already looked at because there is no need to execute it.
                    var assumeCmd = theInfo.Assume;
                    Debug.Assert(assumeCmd != null, "The target block does not start with the expected AssumeCmd");
                    theState.Constraints.AddConstraint(theInfo.ReWrittenAssumeConstraint);

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
                var s = SymbolicPool.GetFreshSymbolic(c, index, CurrentState);
                Debug.Assert(CurrentState.IsInScopeVariable(c.Vars[index]), "Havoc variable is not in scope");
                CurrentState.AssignToVariableInScope(c.Vars[index].Decl, s.Expr);
            }
        }

        protected void Handle(YieldCmd c)
        {
            c.GetInstructionStatistics().IncrementCovered();
            throw new NotImplementedException ();
        }

        protected ExecutionState Fork(ExecutionState stateToFork, ProgramLocation createdAt)
        {
            var newState = stateToFork.Clone(createdAt);

            // Should DeepClone() handle this instead?
            //newState.TreeNode = new ExecutionTreeNode(newState, stateToFork.TreeNode, createdAt);
            ++InternalStatistics.ForkCount;

            // Notify listeners to fork event apart from fork from special
            // `InitialState`.
            if (ForkOccurred != null && stateToFork != InitialState)
            {
                ForkOccurred(this, new ForkEventArgs(stateToFork, newState));
            }
            return newState;
        }

        protected void TransferStateToBlock(ExecutionState state, Block BB)
        {
            Block previous = state.GetCurrentStackFrame().CurrentBlock;
            state.GetCurrentStackFrame().TransferToBlock(BB);
            if (BasicBlockChanged != null)
            {
                BasicBlockChanged(this, new TransferToBlockEventArgs(state, previous, BB));
            }
        }

    }
}

