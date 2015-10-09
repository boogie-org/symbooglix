//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System.Collections.Generic;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Linq;
using System.IO;

namespace Symbooglix
{
    public class Memory : Util.IYAMLWriter
    {
        public Memory()
        {
            Stack = new List<StackFrame>();
            Globals = new SimpleVariableStore();
        }

        public Memory Clone()
        {
            Memory other = (Memory) this.MemberwiseClone();

            other.Stack = new List<StackFrame>();
            foreach (var sf in this.Stack)
            {
                other.Stack.Add(sf.Clone());
            }

            other.Globals = this.Globals.Clone();
            return other;
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            WriteAsYAML(TW, false);
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW, bool showVariables)
        {
            // Globals
            TW.WriteLine("num_globals: {0}", Globals.Count);
            if (showVariables)
            {
                TW.WriteLine("globals:");
                TW.Indent += 1;
                if (Globals.Count == 0)
                {
                    TW.WriteLine("{}"); // Emtpy dictionary
                }
                else
                {
                    foreach (var pair in Globals)
                    {
                        TW.WriteLine("\"{0}\":", pair.Key.ToString());
                        TW.Indent += 1;
                        TW.WriteLine("type: \"{0}\"", pair.Key.TypedIdent.Type);
                        TW.WriteLine("expr: \"{0}\"", pair.Value);
                        TW.Indent -= 1;
                    }
                }
                TW.Indent -= 1;
            }

            // Stackframe
            int depth = Stack.Count;
            TW.WriteLine("stack_depth: {0}", depth);
            TW.WriteLine("stack:");
            TW.Indent += 1;

            for (int index = depth -1; index >= 0; --index)
            {
                TW.WriteLine("-");
                TW.Indent += 1;
                Stack[index].WriteAsYAML(TW, showVariables);
                TW.Indent -= 1;
            }
            TW.Indent -= 1;
        }

        public override string ToString()
        {
            string result = null;
            using (var SW = new StringWriter())
            {
                using (var ITW = new System.CodeDom.Compiler.IndentedTextWriter(SW))
                {
                    WriteAsYAML(ITW);
                }
                result = SW.ToString();
            }
            return result;
        }

        public void PopStackFrame()
        {
            Stack.RemoveAt(Stack.Count - 1);
        }

        public List<StackFrame> Stack;
        public IVariableStore Globals;
    }

    public class StackFrame : Util.IYAMLWriter
    {
        public IVariableStore Locals;
        public Implementation Impl;
        public Procedure Proc;
        public BlockCmdEnumerator CurrentInstruction;

        // FIXME: Make this thread safe
        // Lazy initialisation
        private IVariableStore InternalOldGlobals;
        public IVariableStore OldGlobals
        {
            get
            {
                if (InternalOldGlobals == null)
                {
                    InternalOldGlobals = new SimpleVariableStore();
                }

                return InternalOldGlobals;
            }
            private set { InternalOldGlobals = OldGlobals; }
        }

        public StackFrame(Implementation impl)
        {
            Locals = new SimpleVariableStore();
            InternalOldGlobals = null;
            this.Impl = impl;
            this.Proc = null;
            TransferToBlock(impl.Blocks[0]);
        }

        // This is a dummy stack frame
        public StackFrame(Procedure proc)
        {
            Locals = new SimpleVariableStore();
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

        public StackFrame Clone()
        {
            StackFrame other = (StackFrame) this.MemberwiseClone();

            // procedure/implementation does not need to cloned

            other.Locals = this.Locals.Clone();

            if (this.OldGlobals != null)
                other.InternalOldGlobals = this.InternalOldGlobals.Clone();

            // A dummy stack frame doesn't have an instruction iterator
            if (IsDummy)
                return other;

            // Clone instruction iterator
            other.CurrentInstruction = CurrentInstruction.Clone();

            return other;
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            WriteAsYAML(TW, /*showVariables=*/false);
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW, bool showVariables)
        {
            TW.WriteLine("procedure: \"{0}\"", IsDummy? Proc.Name : Impl.Name);

            if (!IsDummy)
            {
                TW.WriteLine("current_block: \"{0}\"", CurrentBlock);
                TW.Write("current_instruction:");

                if (CurrentInstruction.Current != null)
                {
                    TW.WriteLine("");
                    TW.Indent += 1;
                    // Should we mention the filename too?
                    TW.WriteLine("line: {0}", CurrentInstruction.Current.tok.line);
                    TW.WriteLine("instruction: \"{0}\"", CurrentInstruction.Current.ToString().TrimEnd('\n'));
                    TW.Indent -= 1;
                }
                else
                {
                    TW.WriteLine(" null");
                }
            }

            TW.WriteLine("num_locals: {0}", Locals.Count);
            if (showVariables)
            {
                TW.WriteLine("locals:");

                TW.Indent += 1;
                if (Locals.Count == 0)
                {
                    TW.WriteLine("{}");
                }
                else
                {
                    foreach (var pair in Locals)
                    {
                        TW.WriteLine("\"{0}\":", pair.Key.ToString());
                        TW.Indent += 1;
                        TW.WriteLine("type: \"{0}\"", pair.Key.TypedIdent.Type);
                        TW.WriteLine("expr: \"{0}\"", pair.Value);
                        TW.Indent -= 1;
                    }
                }
                TW.Indent -= 1;
            }
        }

        public override string ToString()
        {
            string result = null;
            using (var SW = new StringWriter())
            {
                using (var ITW = new System.CodeDom.Compiler.IndentedTextWriter(SW))
                {
                    WriteAsYAML(ITW);
                }
                result = SW.ToString();
            }

            return result;
        }

        public void TransferToBlock(Block BB)
        {
            // Update GotoCmd stats
            if (CurrentInstruction != null)
            {
                var gotoCmd = CurrentInstruction.Current as GotoCmd;
                Debug.Assert(gotoCmd != null, "Expected GotoCmd at current instruction");
                (gotoCmd.GetInstructionStatistics() as GotoInstructionStatistics).IncrementJumpTo(BB);
            }

            // Check if BB is in procedure
            Debug.Assert(Impl.Blocks.Contains(BB));

            CurrentBlock = BB;
            CurrentInstruction = new BlockCmdEnumerator(CurrentBlock);
        }
    }

}

