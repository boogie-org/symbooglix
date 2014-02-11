using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;

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
            // Make the first execution state
            currentState = new ExecutionState(entryPoint);
            stateScheduler.addState(currentState);
            
            // FIXME: Check entry point is in prog?

            // FIXME: Loads globals

            // Push entry point onto stack frame
            enterProcedure(entryPoint);

            while (stateScheduler.getNumberOfStates() != 0)
            {
                currentState = stateScheduler.getNextState();
                currentState.getCurrentStackFrame().currentInstruction.MoveNext();
                executeInstruction();
            }
            System.Diagnostics.Debug.WriteLine("Finished executing all states");

            return true;
        }

        public override bool terminate()
        {
            //TODO
            return true;
        }

        private void executeInstruction()
        {
            Absy currentInstruction = currentState.getCurrentStackFrame().currentInstruction.Current;
            if (currentInstruction == null)
                throw new NullReferenceException("Instruction was null");

            if (currentInstruction is Cmd)
            {
                handleSimpleInstruction(currentInstruction as Cmd);
            } else if (currentInstruction is TransferCmd)
            {
                handleTransferCmd(currentInstruction as TransferCmd);
            } else
            {
                throw new NotSupportedException("Unsupported instruction");
            }
        }

        public void enterProcedure(Implementation p)
        {
            Debug.WriteLine("Entering procedure " + p.Name);
            currentState.enterProcedure(p);
        }

        public void leaveProcedure()
        {
            Debug.WriteLine("Leaving Procedure " + currentState.getCurrentStackFrame().procedure.Name);
            currentState.leaveProcedure();

            if (currentState.finished())
                stateScheduler.removeState(currentState);
     
        }

        public void handleSimpleInstruction(Cmd si)
        {
            Debug.WriteLine("Exec: " + si.ToString().TrimEnd('\n'));
        }

        public void handleTransferCmd(TransferCmd ti)
        {
            Console.WriteLine("Exec: " + ti.ToString());

            // FIXME: Do the exit correctly
            leaveProcedure();

        }

    }
}

