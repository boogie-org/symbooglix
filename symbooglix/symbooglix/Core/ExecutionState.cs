using System;

namespace symbooglix
{
    public class ExecutionState
    {
		public Memory mem;

		// FIXME: Loads axioms and types

		// FIXME: Add Path Constraints container

		// FIXME: Add something to track program counter in an elegant way that handles block commands

        public ExecutionState()
        {
        }

		public bool dumpStackTrace()
		{
			// TODO
			return true;
		}

		public bool dumpState()
		{
			return mem.dump();
		}
    }
}

