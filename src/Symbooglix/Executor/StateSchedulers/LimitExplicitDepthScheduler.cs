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
            if (!TerminateIfDepthExceeded(toAdd))
                UnderlyingStateScheduler.AddState(toAdd);
        }

        public void RemoveState(ExecutionState toRemove)
        {
            UnderlyingStateScheduler.RemoveState(toRemove);
        }

        public void RemoveAll(Predicate<ExecutionState> p)
        {
            UnderlyingStateScheduler.RemoveAll(p);
        }

        public int GetNumberOfStates()
        {
            return UnderlyingStateScheduler.GetNumberOfStates();
        }

        public void ReceiveExecutor(Executor executor)
        {
            this.TheExecutor = executor;
            Debug.Assert(TheExecutor != null, "TheExecutor cannot be null");
        }
    }
}

