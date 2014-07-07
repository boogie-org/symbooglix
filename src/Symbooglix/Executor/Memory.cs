using System.Collections.Generic;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Linq;

namespace Symbooglix
{
    public class Memory : Util.IDeepClone<Memory>
    {
        public Memory()
        {
            Stack = new List<StackFrame>();
            Globals = new Dictionary<Variable,Expr>();
        }

        public Memory DeepClone()
        {
            Memory other = (Memory) this.MemberwiseClone();

            other.Stack = new List<StackFrame>();
            foreach (var sf in this.Stack)
            {
                other.Stack.Add(sf.DeepClone());
            }

            var duplicator = new NonSymbolicDuplicator();
            other.Globals = new Dictionary<Variable,Expr>();
            foreach (var pair in this.Globals)
            {
                Expr copy = (Expr) duplicator.Visit(pair.Value);
                other.Globals.Add(pair.Key, copy);
            }

            return other;
        }

        public override string ToString()
        {
            string d = "[Memory]\n";
            string indent = "    ";

            d += indent + "Globals:\n";

            foreach (var tuple in Globals.Keys.Zip(Globals.Values))
            {
                d += indent + tuple.Item1 + ":" + tuple.Item1.TypedIdent.Type  + " := " + tuple.Item2 + "\n";
            }

            d += indent + "\nStack:\n";

            int depth = Stack.Count;
            for (int index = depth -1; index >= 0; --index)
            {
                d += indent + index + ":\n";
                d += Stack [index].ToString();
                d += "\n";
            }

            return d;
        }

        public void PopStackFrame()
        {
            Stack.RemoveAt(Stack.Count - 1);
        }

        public List<StackFrame> Stack;
        public Dictionary<Variable,Expr> Globals;
    }

    public class StackFrame : Util.IDeepClone<StackFrame>
    {
        public Dictionary<Variable,Expr> Locals;
        public Implementation Impl;
        private BlockCmdIterator BCI;
        public IEnumerator<Absy> CurrentInstruction;

        public StackFrame(Implementation impl)
        {
            Locals = new Dictionary<Variable,Expr>();
            this.Impl = impl;
            TransferToBlock(impl.Blocks[0]);
        }

        public Block CurrentBlock
        {
            get;
            private set;
        }

        public StackFrame DeepClone()
        {
            StackFrame other = (StackFrame) this.MemberwiseClone();

            // procedure does not need to cloned
            other.Locals = new Dictionary<Variable, Expr>();
            var duplicator = new NonSymbolicDuplicator();
            foreach (var pair in Locals)
            {
                Expr copy = (Expr) duplicator.Visit(pair.Value);
                other.Locals.Add(pair.Key, copy);
            }

            // Clone instruction iterator
            if (CurrentInstruction.Current is TransferCmd)
            {
                // We are about to transfer so be lazy so don't bother cloning instruction
                Debug.WriteLine("Warning: Not duplicating currentInstruction");
            }
            else
            {
                // FIXME: This is nasty. Find a better way to clone the instruction iterator!
                other.CurrentInstruction = BCI.GetEnumerator(); // new iterator instance

                // Walk the copy forwards until the iterator is pointing to the same instruction
                while (other.CurrentInstruction.Current != this.CurrentInstruction.Current)
                {
                    other.CurrentInstruction.MoveNext();
                }
            }

            return other;
        }

        public override string ToString()
        {
            string d = "[Stack frame for " + Impl.Name + "]\n";
            string indent = "    ";
            d += indent + "Current block :" + CurrentBlock + "\n";
            d += indent + "Current instruction : " + CurrentInstruction.Current + "\n";

            foreach (var tuple in Locals.Keys.Zip(Locals.Values))
            {
                d += indent + tuple.Item1 + ":" + tuple.Item1.TypedIdent.Type + " := " + tuple.Item2 + "\n";
            }

            return d;
        }

        public void TransferToBlock(Block BB)
        {
            Debug.WriteLine("Entering block " + BB.ToString());
            // Check if BB is in procedure
            Debug.Assert(Impl.Blocks.Contains(BB));

            CurrentBlock = BB;
            BCI = new BlockCmdIterator(CurrentBlock);
            CurrentInstruction = BCI.GetEnumerator();
        }
    }

}

