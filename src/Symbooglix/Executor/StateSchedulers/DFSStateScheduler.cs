using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public class DFSStateScheduler : IStateScheduler
    {
        private List<ExecutionState> States;
        public DFSStateScheduler() 
        { 
            States = new List<ExecutionState>();
        }

        public ExecutionState GetNextState() 
        { 
            if (States.Count == 0)
                return null;

            return States[0];
        }

        public void UpdateStates(List<ExecutionState> toAdd, List<ExecutionState> toRemove)
        {
            foreach(ExecutionState e in toRemove)
            {
                Debug.Assert(States.Contains(e));
                States.Remove(e);
            }

            // Add to end of List
            foreach(ExecutionState e in toAdd)
            {
                States.Add(e);
            }
        }

        public int GetNumberOfStates() { return States.Count;}

        public void AddState (ExecutionState toAdd)
        {
            States.Add(toAdd);
        }

        public void RemoveState(ExecutionState toRemove)
        {
            Debug.Assert(States.Contains(toRemove), "Cannot remove state not stored in the state scheduler");
            States.Remove(toRemove);
        }

        public void RemoveAll(Predicate<ExecutionState> p)
        {
            States.RemoveAll(p);
        }
    }
}

