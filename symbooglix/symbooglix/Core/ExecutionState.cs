using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace symbooglix
{
    public class ExecutionState
    {
        public Memory mem;
        private bool started = false;

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

        public StackFrame getCurrentStackFrame()
        {
            return mem.stack.Last();
        }

        public Block getCurrentBlock()
        {
            return getCurrentStackFrame().currentBlock;
        }

        public void enterProcedure(Implementation p)
        {
            started = true;
            StackFrame s = new StackFrame(p, p.Blocks[0]);
            mem.stack.Add(s);
            //blockCmdIterator().Reset(); FIXME we need to reset the iterator when we enter a new procedure
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
            if (started && mem.stack.Count == 0)
                return true;
            else
                return false;
        }

        // FIXME: How is this going to work when we clone execution state or transfer to a different block?
        public IEnumerator<Absy> blockCmdIterator()
        {
            Debug.WriteLine("Entering block " + getCurrentBlock().Label);
            foreach (Cmd c in getCurrentBlock().Cmds)
            {
                Debug.WriteLine("tick");
                yield return c;
            }

            Debug.WriteLine("tick");
            yield return getCurrentBlock().TransferCmd;
        }
    }
}

