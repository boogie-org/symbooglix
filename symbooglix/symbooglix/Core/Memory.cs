using System.Collections.Generic;
using Microsoft.Boogie;
using System.Diagnostics;

namespace symbooglix
{
    public class Memory
    {
        public Memory()
        {
            stack = new List<StackFrame>();
            globals = new Dictionary<GlobalVariable,Expr>();
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
        public Dictionary<GlobalVariable,Expr> globals;
    }

    public class StackFrame
    {
        public Dictionary<Variable,Expr> locals;
        public Implementation procedure;
        private BlockCmdIterator BCI;
        public IEnumerator<Absy> currentInstruction;

        public StackFrame(Implementation procedure)
        {
            locals = new Dictionary<Variable,Expr>();
            this.procedure = procedure;
            transferToBlock(procedure.Blocks[0]);
        }

        public Block currentBlock
        {
            get;
            private set;
        }

        public void transferToBlock(Block BB)
        {
            Debug.WriteLine("Entering block " + BB.ToString());
            // Check if BB is in procedure
            Debug.Assert(procedure.Blocks.Contains(BB));

            currentBlock = BB;
            BCI = new BlockCmdIterator(currentBlock);
            currentInstruction = BCI.GetEnumerator();
        }
    }

}

