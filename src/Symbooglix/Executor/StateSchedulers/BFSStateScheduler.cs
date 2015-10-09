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
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public class BFSStateScheduler : IStateScheduler
    {
        List<ExecutionState> AtDepthEqualToOrLessThanN; // It should usually be N
        List<ExecutionState> AtDepthGreaterThanN; // It should usually be N+1

        int DepthN;

        public BFSStateScheduler()
        {
            AtDepthEqualToOrLessThanN = new List<ExecutionState>();
            AtDepthGreaterThanN= new List<ExecutionState>();
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

        public void RemoveAll()
        {
            AtDepthEqualToOrLessThanN.Clear();
            AtDepthGreaterThanN.Clear();
        }

        public int GetNumberOfStates()
        {
            return AtDepthEqualToOrLessThanN.Count + AtDepthGreaterThanN.Count;
        }

        public void ReceiveExecutor(Executor executor)
        {
            // Not needed
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            TW.WriteLine("name : \"{0}\"", this.GetType().ToString());
            TW.WriteLine("depth: {0}", this.DepthN);
        }
    }
}

