using System.Collections.Generic;

namespace symbooglix
{
    public class Memory
    {
        public Memory()
        {
        }

        public bool dump()
        {
            // TODO:
            return true;
        }

        public List<StackFrame> stack;
        public List<MemoryObject> globals;
    }

    public class StackFrame
    {
        public List<MemoryObject> locals;
    }

    public class MemoryObject
    {
        public MemoryObject() { }
    }
}

