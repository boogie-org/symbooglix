using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public class BFSStateScheduler : IStateScheduler
    {
        List<ExecutionState> L1;
        List<ExecutionState> L2;

        List<ExecutionState> AtDepthEqualToOrLessThanN; // It should usually be N
        List<ExecutionState> AtDepthGreaterThanN; // It should usually be N+1

        int DepthN;

        public BFSStateScheduler()
        {
            L1 = new List<ExecutionState>();
            L2 = new List<ExecutionState>();

            AtDepthEqualToOrLessThanN = L1;
            AtDepthGreaterThanN = L2;
            DepthN = 0;
        }

        private void IncreaseDepth()
        {
            var temp = AtDepthEqualToOrLessThanN;
            AtDepthEqualToOrLessThanN = AtDepthGreaterThanN;
            AtDepthGreaterThanN = temp;
            ++DepthN;
        }

        public ExecutionState GetNextState()
        {
            while (AtDepthEqualToOrLessThanN.Count > 0)
            {
                // FIXME: Using a list probably isn't very efficient here
                // we should use a Queue instead
                var stateToExecute = AtDepthEqualToOrLessThanN[0];
                if (stateToExecute.ExplicitBranchDepth > DepthN)
                {
                    // The state has gone too deep move to other List
                    AtDepthEqualToOrLessThanN.RemoveAt(0);
                    AtDepthGreaterThanN.Add(stateToExecute);
                }
                else
                    return stateToExecute;
            }

            Debug.Assert(AtDepthEqualToOrLessThanN.Count == 0);

            if (AtDepthGreaterThanN.Count == 0)
            {
                // There are no more states to execute
                return null;
            }

            // We have evaluated all states that are up to DepthN deep
            // we can now go deeper. We achieve this by swapping the lists round
            IncreaseDepth();
            return GetNextState();
        }

        public void AddState(ExecutionState toAdd)
        {
            Debug.Assert(!AtDepthEqualToOrLessThanN.Contains(toAdd), "A state already in the scheduler should not be added");
            Debug.Assert(!AtDepthGreaterThanN.Contains(toAdd), "A state already in the scheduler should not be added");

            if (toAdd.ExplicitBranchDepth <= DepthN)
                AtDepthEqualToOrLessThanN.Add(toAdd);
            else
                AtDepthGreaterThanN.Add(toAdd);
        }

        public void RemoveState(ExecutionState toRemove)
        {
            Debug.Assert(AtDepthEqualToOrLessThanN.Contains(toRemove) || AtDepthGreaterThanN.Contains(toRemove), "Cannot remove a state not in the scheduler");
            bool success = AtDepthEqualToOrLessThanN.Remove(toRemove);

            if (!success)
                success = AtDepthGreaterThanN.Remove(toRemove);
        }

        public void RemoveAll(Predicate<ExecutionState> p)
        {
            AtDepthEqualToOrLessThanN.RemoveAll(p);
            AtDepthGreaterThanN.RemoveAll(p);
        }

        public int GetNumberOfStates()
        {
            return AtDepthEqualToOrLessThanN.Count + AtDepthGreaterThanN.Count;
        }
    }
}

