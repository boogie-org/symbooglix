using System.Collections.Generic;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Linq;
using System.IO;

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

        public void Dump(TextWriter TW, int indent)
        {
            TW.WriteLine("[Memory]");
            string indentStr = new string(' ',indent);

            TW.WriteLine("Globals (" + Globals.Count + "):");

            foreach (var tuple in Globals.Keys.Zip(Globals.Values))
            {
                TW.WriteLine(indentStr + tuple.Item1 + ":" + tuple.Item1.TypedIdent.Type  + " := " + tuple.Item2);
            }

            TW.WriteLine("");

            TW.WriteLine("Stack (" + Stack.Count + "):");

            int depth = Stack.Count;
            for (int index = depth -1; index >= 0; --index)
            {
                TW.WriteLine(indentStr + index + ":");
                Stack[index].Dump(TW, indent);
                TW.WriteLine("");
            }
        }

        public override string ToString()
        {
            string result = null;
            using (var SW = new StringWriter())
            {
                Dump(SW, 4);
                result = SW.ToString();
            }
            return result;
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
        public Procedure Proc;
        public BlockCmdEnumerator CurrentInstruction;

        // FIXME: Make this thread safe
        // Lazy initialisation
        private Dictionary<GlobalVariable, Expr> InternalOldGlobals;
        public Dictionary<GlobalVariable, Expr> OldGlobals
        {
            get
            {
                if (InternalOldGlobals == null)
                {
                    InternalOldGlobals = new Dictionary<GlobalVariable, Expr>();
                }

                return InternalOldGlobals;
            }
            private set { InternalOldGlobals = OldGlobals; }
        }

        public StackFrame(Implementation impl)
        {
            Locals = new Dictionary<Variable,Expr>();
            InternalOldGlobals = null;
            this.Impl = impl;
            this.Proc = null;
            TransferToBlock(impl.Blocks[0]);
        }

        // This is a dummy stack frame
        public StackFrame(Procedure proc)
        {
            Locals = new Dictionary<Variable,Expr>();
            InternalOldGlobals = null;
            this.Proc = proc;
            this.Impl = null;
            this.CurrentInstruction = null;
        }

        public bool IsDummy
        {
            get { return this.Impl == null && this.CurrentInstruction == null; }
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

            if (this.OldGlobals != null)
            {
                other.InternalOldGlobals = new Dictionary<GlobalVariable, Expr>();
                foreach (var pair in this.OldGlobals)
                {
                    Expr copy = (Expr) duplicator.Visit(pair.Value);
                    other.InternalOldGlobals.Add(pair.Key, copy);
                }
            }

            // A dummy stack frame doesn't have an instruction iterator
            if (IsDummy)
                return other;

            // Clone instruction iterator
            other.CurrentInstruction = CurrentInstruction.DeepClone();

            return other;
        }

        public void Dump(TextWriter TW, int indent)
        {
            if (IsDummy)
            {
                TW.WriteLine("[Dummy Stack frame for " + Proc.Name + "]");
                return;
            }

            string indentStr = new string(' ', indent);

            TW.WriteLine("[Stack frame for " + Impl.Name + "]");
            TW.WriteLine(indentStr + "Current block :" + CurrentBlock);
            TW.WriteLine(indentStr + "Current instruction : (" + 
                         CurrentInstruction.Current.tok.filename + ":" +
                         CurrentInstruction.Current.tok.line + ") " +
                         CurrentInstruction.Current.ToString().TrimEnd('\n')
                        );
            TW.WriteLine("");

            foreach (var tuple in Locals.Keys.Zip(Locals.Values))
            {
                TW.WriteLine(indentStr + tuple.Item1 + ":" + tuple.Item1.TypedIdent.Type + " := " + tuple.Item2);
            }
        }

        public override string ToString()
        {
            string result = null;
            using (var SW = new StringWriter())
            {
                Dump(SW, 4);
                result = SW.ToString();
            }

            return result;
        }

        public void TransferToBlock(Block BB)
        {
            Debug.WriteLine("Entering block " + BB.ToString());
            // Check if BB is in procedure
            Debug.Assert(Impl.Blocks.Contains(BB));

            CurrentBlock = BB;
            CurrentInstruction = new BlockCmdEnumerator(CurrentBlock);
        }
    }

}

