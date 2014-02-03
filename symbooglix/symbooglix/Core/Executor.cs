using System;
using Microsoft.Boogie;
using System.Collections.Generic;

namespace symbooglix
{
	public abstract class AExecutor
    {
		public AExecutor(Program prog) { this.prog = prog;} //FIXME: make copy so it possible to have multiple executors running in parallel

		public abstract bool prepare(); // Modify program to make it suitable for execution
		public abstract bool run(Implementation entryPoint);
		public abstract bool terminate();

		protected Program prog;
    }

	public class PrintingExecutor : AExecutor
	{
		public PrintingExecutor(Program prog, IStateScheduler scheduler) : base(prog) { stateScheduler = scheduler; }

		private IStateScheduler stateScheduler;
		private ExecutionState currentState;

		public override bool prepare()
		{
			// TODO
			return true;
		}

		public override bool run(Implementation entryPoint)
		{
            Console.WriteLine("Entering `" + entryPoint.Id + "`"
                              );
            // Make the first execution state
            currentState = new ExecutionState();
            stateScheduler.addState(currentState);
			
            // FIXME: Check entry point is in prog?

            // FIXME: Loads globals

            // Push entry point onto stack frame
            enterFunction(entryPoint);

            while (stateScheduler.getNumberOfStates() != 0)
            {
                currentState = stateScheduler.getNextState();
                executeInstruction(currentState);
            }
            System.Diagnostics.Debug.Write("Finished executing all states");

			return true;
		}

		public override bool terminate()
		{
			//TODO
			return true;
		}

		private bool executeInstruction(ExecutionState e)
		{
			// TODO
			return true;
		}

        public void enterFunction(Implementation f)
        {

        }

	}
}

