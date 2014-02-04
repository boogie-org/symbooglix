using System;
using Microsoft.Boogie;
using System.Collections.Generic;

namespace symbooglix
{
    public class ExecutionState
    {
        public Block currentBlock
        {
            get;
            private set;
        }

        public Memory mem;

        // FIXME: Loads axioms and types

        // FIXME: Add Path Constraints container

        // FIXME: Add something to track program counter in an elegant way that handles block commands

        public ExecutionState(Implementation entryPoint)
        {
            mem = new Memory();

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

        public void enterProcedure(Implementation p)
        {
            StackFrame s = new StackFrame(p);
            mem.stack.Add(s);
            currentBlock = p.Blocks[0];
            //blockCmdIterator().Reset(); FIXME
            blockCmdIterator().MoveNext(); // Executor expects that Current is first instruction
        }

        public void leaveProcedure()
        {
            if (finished())
                throw new InvalidOperationException("Not currently in procedure");

            mem.popStackFrame();

        }

        public bool finished()
        {
            // FIXME: We should not return true when the state has just been created.
            if (mem.stack.Count == 0)
                return true;
            else
                return false;
        }

        // FIXME: How is this going to work when we clone execution state?
        public IEnumerator<Absy> blockCmdIterator()
        {
            foreach (Cmd c in currentBlock.Cmds)
            {
                Console.WriteLine("tick");
                yield return c;
            }

            Console.WriteLine("tick");
            yield return currentBlock.TransferCmd;
        }
    }
}

