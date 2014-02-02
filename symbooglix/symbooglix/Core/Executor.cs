using System;
using Microsoft.Boogie;
using System.Collections.Generic;

namespace symbooglix
{
	public abstract class AExecutor
    {
		public AExecutor(Program prog) { this.prog = prog;} //FIXME: make copy

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

			// Check entry point is in prog?

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

	}
}

