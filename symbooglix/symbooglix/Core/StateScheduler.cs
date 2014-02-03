using System;
using System.Collections.Generic;

namespace symbooglix
{
    public interface IStateScheduler
    {
		ExecutionState getNextState(); // FIXME: Return reference
		bool updateStates(List<ExecutionState> toAdd, List<ExecutionState> toRemove); //FIXME: pass by ref
        bool addState(ExecutionState toAdd);
        bool removeState(ExecutionState toRemove);
		int getNumberOfStates();
    }

	public class DFSStateScheduler : IStateScheduler
	{
		private List<ExecutionState> states;
		public DFSStateScheduler() 
        { 
            states = new List<ExecutionState>();
        }

		public ExecutionState getNextState() 
		{ 
			if (states.Count == 0)
				return null;

			return states[0];	
		}

		public bool updateStates(List<ExecutionState> toAdd, List<ExecutionState> toRemove)
		{
			// FIXME: How do we comparisions with refs??
			foreach(ExecutionState e in toRemove)
			{
				states.Remove(e);
			}

			// Add to end of List
			foreach(ExecutionState e in toAdd)
			{
				states.Add(e);
			}

			return true; // FIXME : Can we fail?
		}

		public int getNumberOfStates() { return states.Count;}

        public bool addState (ExecutionState toAdd)
        {
            states.Add(toAdd);
            return true;
        }

        public bool removeState (ExecutionState toRemove)
        {
            throw new NotImplementedException ();
        }
	}
}

