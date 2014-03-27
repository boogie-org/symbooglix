using System.Collections.Generic;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Linq;

namespace symbooglix
{
    public class Memory : util.IDeepClone<Memory>
    {
        public Memory()
        {
            stack = new List<StackFrame>();
            globals = new Dictionary<Variable,Expr>();
        }

        public Memory DeepClone()
        {
            Memory other = (Memory) this.MemberwiseClone();

            other.stack = new List<StackFrame>();
            foreach (var sf in this.stack)
            {
                other.stack.Add(sf.DeepClone());
            }

            var duplicator = new Duplicator();
            other.globals = new Dictionary<Variable,Expr>();
            foreach (var pair in this.globals)
            {
                Expr copy = (Expr) duplicator.Visit(pair.Value);
                other.globals.Add(pair.Key, copy);
            }

            return other;
        }

        public override string ToString()
        {
            string d = "[Memory]\n";
            string indent = "    ";

            d += indent + "Globals:\n";

            foreach (var tuple in globals.Keys.Zip(globals.Values))
            {
                d += indent + tuple.Item1 + ":" + tuple.Item1.TypedIdent.Type  + " := " + tuple.Item2 + "\n";
            }

            d += indent + "\nStack:\n";

            int depth = stack.Count;
            for (int index = depth -1; index >= 0; --index)
            {
                d += indent + index + ":\n";
                d += stack [index].ToString();
                d += "\n";
            }

            return d;
        }

        public void popStackFrame()
        {
            stack.RemoveAt(stack.Count - 1);
        }

        public List<StackFrame> stack;
        public Dictionary<Variable,Expr> globals;
    }

    public class StackFrame : util.IDeepClone<StackFrame>
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

        public StackFrame DeepClone()
        {
            StackFrame other = (StackFrame) this.MemberwiseClone();

            // procedure does not need to cloned
            other.locals = new Dictionary<Variable, Expr>();
            var duplicator = new Duplicator();
            foreach (var pair in locals)
            {
                Expr copy = (Expr) duplicator.Visit(pair.Value);
                other.locals.Add(pair.Key, copy);
            }

            // Clone instruction iterator
            if (currentInstruction.Current is TransferCmd)
            {
                // We are about to transfer so be lazy so don't bother cloning instruction
                Debug.Write("Warning: Not duplicating currentInstruction");
            }
            else
            {
                // FIXME: This is nasty. Find a better way to clone the instruction iterator!
                other.currentInstruction = BCI.GetEnumerator(); // new iterator instance

                // Walk the copy forwards until the iterator is pointing to the same instruction
                do
                {
                    other.currentInstruction.MoveNext();
                } while (other.currentInstruction.Current != this.currentInstruction.Current);
            }

            return other;
        }

        public override string ToString()
        {
            string d = "[Stack frame for " + procedure.Name + "]\n";
            string indent = "    ";
            d += indent + "Current block :" + currentBlock + "\n";
            d += indent + "Current instruction : " + currentInstruction.Current + "\n";

            foreach (var tuple in locals.Keys.Zip(locals.Values))
            {
                d += indent + tuple.Item1 + ":" + tuple.Item1.TypedIdent.Type + " := " + tuple.Item2 + "\n";
            }

            return d;
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

