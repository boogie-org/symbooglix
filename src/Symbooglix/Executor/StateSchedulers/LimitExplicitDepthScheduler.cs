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
using System.Diagnostics;

namespace Symbooglix
{
    public class LimitExplicitDepthScheduler :IStateScheduler
    {
        IStateScheduler UnderlyingStateScheduler;
        Executor TheExecutor= null;
        int MaxDepth;
        public LimitExplicitDepthScheduler(IStateScheduler underlyingScheduler, int maxDepth)
        {
            this.UnderlyingStateScheduler = underlyingScheduler;
            this.MaxDepth = maxDepth;
        }

        private bool TerminateIfDepthExceeded(ExecutionState state)
        {
            if (state.ExplicitBranchDepth > MaxDepth)
            {
                // Don't remove from the UnderlyingStateScheduler here as it might not have been added to the UnderlyingStateScheduler

                Debug.Assert(TheExecutor != null, "TheExecutor cannot be null");
                // Estimate where we terminate
                var programLoc = state.GetCurrentStackFrame().CurrentInstruction.Current.GetProgramLocation(); 
                TheExecutor.TerminateState(state, new TerminatedWithDisallowedExplicitBranchDepth(programLoc), /*removeFromStateScheduler=*/ false);
                return true;
            }
            else
                return false;
        }

        public ExecutionState GetNextState()
        {
            while (GetNumberOfStates() > 0)
            {
                var state = UnderlyingStateScheduler.GetNextState();

                if (!TerminateIfDepthExceeded(state))
                    return state;
                else
                    UnderlyingStateScheduler.RemoveState(state);
            }

            Debug.Assert(GetNumberOfStates() == 0, "Expected no states to remain");
            return null;
        }

        public void AddState(ExecutionState toAdd)
        {
            // Don't remove state here even if its ExplicitBranchDepth is greater than what is allowed.
            // If we terminate it here this leads to very unintuitive behaviour because
            // it might be (and usually is) the case that toAdd is not currently being executed
            // by the Executor as so terminating a state that isn't being executed or about to be
            // Executed can be confusing.
            UnderlyingStateScheduler.AddState(toAdd);
        }

        public void RemoveState(ExecutionState toRemove)
        {
            UnderlyingStateScheduler.RemoveState(toRemove);
        }

        public void RemoveAll()
        {
            UnderlyingStateScheduler.RemoveAll();
        }

        public int GetNumberOfStates()
        {
            return UnderlyingStateScheduler.GetNumberOfStates();
        }

        public void ReceiveExecutor(Executor executor)
        {
            this.TheExecutor = executor;
            Debug.Assert(TheExecutor != null, "TheExecutor cannot be null");
            UnderlyingStateScheduler.ReceiveExecutor(executor);
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            TW.WriteLine("name : \"{0}\"", this.GetType().ToString());
            TW.WriteLine("max_depth: {0}", this.MaxDepth);
            TW.WriteLine("underlying_scheduler:");
            TW.Indent += 1;
            UnderlyingStateScheduler.WriteAsYAML(TW);
            TW.Indent -= 1;
        }
    }
}

