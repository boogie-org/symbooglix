using System.Collections.Generic;
using Microsoft.Boogie;

namespace symbooglix
{
    public class Memory
    {
        public Memory()
        {
            stack = new List<StackFrame>();
            globals = new List<MemoryObject>();
        }

        public bool dump()
        {
            // TODO:
            return true;
        }

        public void popStackFrame()
        {
            stack.RemoveAt(stack.Count - 1);
        }

        public List<StackFrame> stack;
        public List<MemoryObject> globals;
    }

    public class StackFrame
    {
        public List<MemoryObject> locals;
        public Implementation procedure;

        public StackFrame(Implementation procedure, Block BB)
        {
            locals = new List<MemoryObject>();
            this.procedure = procedure;
            currentBlock = BB;
        }

        public Block currentBlock
        {
            get;
            private set;
        }
    }

    public class MemoryObject
    {
        public MemoryObject() { }
    }
}

