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
        public List<SymbolicVariable> symbolics;

        // FIXME: Loads axioms and types

        // FIXME: Add Path Constraints container

        // FIXME: Add something to track program counter in an elegant way that handles block commands

        public ExecutionState()
        {
            mem = new Memory();
            symbolics = new List<SymbolicVariable>();
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
            StackFrame s = new StackFrame(p);
            mem.stack.Add(s);
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

    }
}

