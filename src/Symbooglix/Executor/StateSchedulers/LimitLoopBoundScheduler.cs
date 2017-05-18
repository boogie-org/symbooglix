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
using System.Numerics;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Linq;

namespace Symbooglix
{
    public class LimitLoopBoundScheduler : IStateScheduler
    {
        IStateScheduler UnderlyingScheduler;
        Dictionary<ExecutionState, ExecutionStateNestedLoopInfo> StateToCurrentLoops;
        public readonly BigInteger LoopBound;
        protected Executor Executor;
        public ProgramLoopInfo ProgramLoopInfo { get; private set; }
        public LimitLoopBoundScheduler(IStateScheduler underlyingScheduler, BigInteger loopBound)
        {
            this.UnderlyingScheduler = underlyingScheduler;
            this.LoopBound = loopBound;
            if (this.LoopBound < 0)
            {
                throw new ArgumentException("Invalid loop bound");
            }
            this.StateToCurrentLoops = new Dictionary<ExecutionState, ExecutionStateNestedLoopInfo>();
            this.ProgramLoopInfo = null; // Set elsewhere
            this.Executor = null; // Set elsewhere
        }

        private bool InitLoopInfoFor(ExecutionState state)
        {
            if (StateToCurrentLoops.ContainsKey(state))
                return false;
            StateToCurrentLoops.Add(state, new ExecutionStateNestedLoopInfo(state));
            return true;
        }

        public ExecutionState GetNextState()
        {
            ExecutionState state = UnderlyingScheduler.GetNextState();
            while (state != null)
            {
                if (!CheckLoopBoundExceeded(state))
                {
                    // Still in bounds.
                    return state;
                }
                // Bound exceeded
                // Get location for termination
                var currentInstruction = state.Mem.Stack.Last().CurrentInstruction;
                // FIXME: This is an implementation detail of the Executor that we shouldn't
                // have to deal with.
                if (currentInstruction.Current == null)
                    currentInstruction.MoveNext();

                var progLocation = currentInstruction.Current.GetProgramLocation();
                var terminationType = new TerminatedWithDisallowedLoopBound(progLocation, LoopBound);
                // Kill state and let the Executor call us to remove the states.
                Executor.TerminateState(/*state=*/ state, /*type=*/ terminationType, /*removeFromStateScheduler=*/true);

                // Try another state
                state = UnderlyingScheduler.GetNextState();
            }
            return null;
        }

        public void AddState(ExecutionState toAdd)
        {
            InitLoopInfoFor(toAdd);
            UnderlyingScheduler.AddState(toAdd);
        }

        public void RemoveState(ExecutionState toRemove)
        {
            StateToCurrentLoops.Remove(toRemove);
            UnderlyingScheduler.RemoveState(toRemove);
        }

        public void RemoveAll()
        {
            StateToCurrentLoops.Clear();
            UnderlyingScheduler.RemoveAll();
        }

        public int GetNumberOfStates()
        {
            return UnderlyingScheduler.GetNumberOfStates();
        }

        public void ReceiveExecutor(Executor executor)
        {
            this.Executor = executor;
            // Guard just in case the Executor calls us again. This can
            // happen if there are multiple entry points.
            if (this.ProgramLoopInfo == null)
            {
                this.ProgramLoopInfo = new ProgramLoopInfo(executor.TheProgram);

                // Register the callbacks we need
                executor.BasicBlockChanged += Executor_BasicBlockChanged;
                executor.ForkOccurred += Executor_ForkOccurred;
                executor.ImplementationEntered += Executor_ImplementationEntered;
            }

            // Give the underlying executor access to the scheduler
            UnderlyingScheduler.ReceiveExecutor(executor);
        }

        void Executor_ImplementationEntered(object sender, Symbooglix.Executor.EnterImplementationEventArgs e)
        {
            // Handle the case where we enter a new implementation and the first block
            // is a loop header. This is the only case we don't get notified of a basic block
            // change.
            var state = Executor.CurrentState; // FIXME: The state should be part of the event arg
            var sf = state.Mem.Stack.Last();
            var loopInfo = ProgramLoopInfo.GetLoopInfoForHeader(sf.CurrentBlock);
            if (loopInfo == null)
                return; // Not a loop. Nothing to do.
            var executionStateSingleLoopInfo = new ExecutionStateSingleLoopInfo(sf, loopInfo);
            StateToCurrentLoops[state].NestedLoops.Push(executionStateSingleLoopInfo);
        }

        void Executor_BasicBlockChanged(object sender, Symbooglix.Executor.TransferToBlockEventArgs eventArgs)
        {
            // Control flow has transferred to a different basic block
            var state = eventArgs.State;
            var sf = state.Mem.Stack.Last();
            var executionStateNestedLoopInfo = StateToCurrentLoops[state];
            // Cases:
            // * No existing loops, enter loop header
            // * No existing loops, do not enter loop header
            // * Existing loop, stackframe doesn't match (i.e. a call must have happenend), enter loop header
            // * Existing loop, stackframe doesn't match (i.e. a call must have happenend), do not enter loop header
            // * Existing loop, stackframe matches, enter loop header (must increment counter)
            // * Existing loop, stackframe matches, leave loop via exit basic block (we are leaving the current loop)
            // * Existing loop, stackframe matches, enter nested loop header (must push new loop on to stack)
            // * Existing loop, stackframe matches, stay in current loop (nothing to do)

            bool stackframeMatches = false;
            if (executionStateNestedLoopInfo.NestedLoops.Count > 0)
            {
                stackframeMatches = object.ReferenceEquals(executionStateNestedLoopInfo.NestedLoops.Peek().Stack,
                                                           sf);
            }

            ExecutionStateSingleLoopInfo executionStateSingleLoopInfo = null;
            if (!stackframeMatches)
            {
                // This handles the case that there are no existing loops on the stack or
                // there are existing loops but they are in another stackframe (i.e. we were in a loop
                // and then called into another implementation).
                var loopInfo = ProgramLoopInfo.GetLoopInfoForHeader(eventArgs.NewBlock);
                if (loopInfo == null)
                {
                    // The block we've entered is not a loop header and there are no
                    // existing loops we are in that we can enter/exit so there is nothing
                    // left to do
                    return;
                }
                // We've enterred a new loop push it on to the loop stack
                executionStateSingleLoopInfo = new ExecutionStateSingleLoopInfo(sf, loopInfo);
                executionStateNestedLoopInfo.NestedLoops.Push(executionStateSingleLoopInfo);
                return;
            }

            // We are currently inside a loop and are still in the context of that loop's stackframe on the
            // call stack.
            executionStateSingleLoopInfo = executionStateNestedLoopInfo.NestedLoops.Peek();
            if (object.ReferenceEquals(executionStateSingleLoopInfo.LInfo.Header, eventArgs.NewBlock)) {
                // We are going to the loop header so we must have just completed one iteration
                // of the loop. Increment the counter.
                executionStateSingleLoopInfo.IncrementCounter();

                // Don't check bound here. The executor will misbehave (see goto look ahead)
                // if we try to terminate state here.
                return;
            } 
            else if (executionStateSingleLoopInfo.LInfo.EscapingBlocks.Contains(eventArgs.NewBlock))
            {
                // We are in a loop but are about to jump to a basic block that escapes from the loop.
                // So pop this loop from the stack.
                executionStateNestedLoopInfo.NestedLoops.Pop();
                return;
            }
            var newLoopInfo = ProgramLoopInfo.GetLoopInfoForHeader(eventArgs.NewBlock);
            if (newLoopInfo == null)
            {
                // We are in a loop but we are jumping to a basic block that 
                // * does not escape the current loop
                // * does not go to the loop head
                // * does not enter a nested loop (i.e. another loop head)
                // So there is nothing left to do.
                return;
            }

            // We are entering a nested loop. Push this loop onto the stack.
            var newExecutionStateSingleLoopInfo = new ExecutionStateSingleLoopInfo(sf, newLoopInfo);
            executionStateNestedLoopInfo.NestedLoops.Push(newExecutionStateSingleLoopInfo);
            return;
        }

        bool CheckLoopBoundExceeded(ExecutionState state)
        {
            var executionStateNestedLoopInfo = StateToCurrentLoops[state];
            if (executionStateNestedLoopInfo.NestedLoops.Count == 0)
                return false;

            if (executionStateNestedLoopInfo.NestedLoops.Peek().Counter <= LoopBound)
                return false;

            // Loop bound exceeded
            return true;
        }

        void Executor_ForkOccurred(object sender, Symbooglix.Executor.ForkEventArgs eventArgs)
        {
            if (StateToCurrentLoops.ContainsKey(eventArgs.Child))
                throw new ArgumentException("Child ExecutionState should not already be stored");
            if (!StateToCurrentLoops.ContainsKey(eventArgs.Parent))
                throw new ArgumentException("Parent ExecutionState should have been stored already");
            // Make a copy of the parent's `ExecutionStateNestedLoopInfo` but replace
            // references to stackframes so they point to the child's
            var childLoopInfo = StateToCurrentLoops[eventArgs.Parent].Clone(eventArgs.Child);
            StateToCurrentLoops.Add(eventArgs.Child, childLoopInfo);
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            TW.WriteLine("name : \"{0}\"", this.GetType().ToString());
            TW.WriteLine("loop_bound: {0}", this.LoopBound);
            TW.WriteLine("underlying_scheduler:");
            TW.Indent += 1;
            UnderlyingScheduler.WriteAsYAML(TW);
            TW.Indent -= 1;
        }
    }
}

