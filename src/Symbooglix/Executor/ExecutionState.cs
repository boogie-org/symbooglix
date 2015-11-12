//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;
using System.IO;

namespace Symbooglix
{
    public class ExecutionState : Util.IYAMLWriter
    {
        public Memory Mem;
        public IConstraintManager Constraints;
        public int Id
        {
            get;
            private set;
        }

        public ITerminationType TerminationType
        {
            get;
            private set;
        }

        public ExecutionTreeNode TreeNode
        {
            get;
            internal set;
        }

        public ProgramLocation CreatedAt
        {
            get;
            private set;
        }

        /// <summary>
        /// Gets the explicit branch depth. This is considered to be the number of goto
        /// instructions the state has executed past that have more than one target.
        /// </summary>
        /// <value>The explicit branch depth.</value>
        public int ExplicitBranchDepth
        {
            get;
            private set;
        }

        public void IncrementExplicitBranchDepth()
        {
            ++ExplicitBranchDepth;
        }

        /// <summary>
        /// An execution is consider speculative if a path has been followed
        /// that the Solver could not prove could be followed (i.e. it returned unknown)
        /// </summary>
        public bool Speculative
        {
            get;
            private set;
        }

        /// <summary>
        /// Gets the location at which the execution state became speculative
        /// </summary>
        public ProgramLocation SpeculativeStart
        {
            get;
            private set;
        }

        public void MakeSpeculative(ProgramLocation loc)
        {
            Speculative = true;
            Debug.Assert(loc != null);
            SpeculativeStart = loc;
        }

        // Start at -1 so the executor can keep around the special "-1" state that will never enter any procedure
        private static int NewId = -1;

        public ExecutionState()
        {
            Mem = new Memory();
            Constraints = new ConstraintManager();
            Id = NewId++;
            TerminationType = null;
            Speculative = false;
            ExplicitBranchDepth = 0;
            TreeNode = null; //new ExecutionTreeNode(this, null, null); // FIXME: Disabled due to design issues.
            CreatedAt = null;

        }

        public ExecutionState Clone(ProgramLocation loc)
        {
            ExecutionState other = (ExecutionState) this.MemberwiseClone();
            other.Mem = this.Mem.Clone();


            other.Id = NewId++;

            other.Constraints = this.Constraints.Clone();
            other.CreatedAt = loc;
            return other;
        }

        public bool DumpStackTrace()
        {
            // TODO
            return true;
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            WriteAsYAML(TW, false, false);
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW, bool showConstraints, bool showVariables)
        {
            TW.WriteLine("state_id: {0}", this.Id);
            TW.Write("status:");
            if (Finished())
            {
                // Nested dictionary
                TW.Indent += 1;
                TW.WriteLine("");
                TW.WriteLine("message: \"{0}\"", this.TerminationType.GetMessage());

                var exitLoc = this.TerminationType.ExitLocation;
                TW.WriteLine("line_num: {0}", exitLoc.LineNumber);
                TW.WriteLine("termination_type: \"{0}\"", this.TerminationType.GetType().ToString());
                TW.Indent -= 1;
            }
            else
            {
                TW.WriteLine(" \"running\"");
            }

            TW.Write("created_at:");
            if (CreatedAt == null)
                TW.WriteLine(" null");
            else
            {
                TW.Indent += 1;
                TW.WriteLine("");
                TW.WriteLine("line_num: {0}", CreatedAt.LineNumber);
                // FIXME: The line should be escaped to be YAML compatible
                TW.WriteLine("line: \"{0}\"", CreatedAt.Line);
                TW.Indent -= 1;
            }

            TW.WriteLine("explicit_branch_depth: {0}", this.ExplicitBranchDepth.ToString().ToLower());
            TW.WriteLine("speculative: {0}", this.Speculative.ToString().ToLower());

            // write memory
            TW.WriteLine("memory:");
            TW.Indent += 1;
            Mem.WriteAsYAML(TW, showVariables);
            TW.Indent -= 1;

            // Write constraints
            TW.WriteLine("constraints:");
            TW.Indent += 1;
            Constraints.WriteAsYAML(TW, showConstraints);
            TW.Indent -= 1;

        }


       
        public StackFrame GetCurrentStackFrame()
        {
            if (Mem.Stack.Count == 0)
                return null;
            else
                return Mem.Stack.Last();
        }

        public Block GetCurrentBlock()
        {
            var sf = GetCurrentStackFrame();

            if (sf == null)
                return null;
            else
                return sf.CurrentBlock;
        }

        public void EnterImplementation(Implementation impl)
        {
            StackFrame s = new StackFrame(impl);
            Mem.Stack.Add(s);
        }

        // Returns variable Expr if in scope, otherwise
        // return null
        public Expr GetInScopeVariableExpr(Variable v)
        {
            // Only the current stackframe is in scope
            if (GetCurrentStackFrame().Locals.ContainsKey(v))
            {
                return GetCurrentStackFrame().Locals [v];
            }

            if (v is GlobalVariable || v is Constant)
            {
                // If not in stackframe look through globals
                if (Mem.Globals.ContainsKey(v))
                {
                    return Mem.Globals[v];
                }
            }

            return null;
        }

        public KeyValuePair<Variable,Expr> GetInScopeVariableAndExprByName(string name)
        {
            var local = ( from pair in GetCurrentStackFrame().Locals
                         where pair.Key.Name == name
                         select pair );
            if (local.Count() != 0)
            {
                Debug.Assert(local.Count() == 1);
                return local.First();
            }

            var global = ( from pair in Mem.Globals
                          where pair.Key.Name == name
                          select pair );

            Debug.Assert(global.Count() == 1, "The requested global was not found");
            var kp = global.First();
            return new KeyValuePair<Variable,Expr>( (Variable) kp.Key, kp.Value);
        }

  
        public bool AssignToVariableInStack(StackFrame s, Variable v, Expr value)
        {
            Debug.Assert(Mem.Stack.Contains(s));

            if (s.Locals.ContainsKey(v))
            {
                s.Locals [v] = value;
                return true;
            }
            return false;

        }

        public bool IsInScopeVariable(Variable v)
        {
            if (GetCurrentStackFrame().Locals.ContainsKey(v))
                return true;

            if (v is GlobalVariable || v is Constant)
            {
                if (Mem.Globals.ContainsKey(v))
                    return true;
            }

            return false;
        }

        public bool IsInScopeVariable(IdentifierExpr i)
        {
            return IsInScopeVariable(i.Decl);
        }

        public void AssignToVariableInScope(Variable v, Expr value)
        {
            Debug.Assert(!(v is Constant), "Cannot assign to a constant");

            if (AssignToVariableInStack(GetCurrentStackFrame(), v, value))
                return;

            if (v is GlobalVariable)
            {
                var g = v as GlobalVariable;
                AssignToGlobalVariable(g, value);
                return;
            }

            throw new InvalidOperationException("Cannot assign to variable not in scope.");
        }

        public void AssignToMapVariableInScopeAt(Variable v, IList<Expr> indices, Expr value)
        {
            if (v is GlobalVariable)
            {
                Mem.Globals.WriteMap(v, indices, value);
                return;
            }

            // Must be a local variable
            var sf = GetCurrentStackFrame();
            sf.Locals.WriteMap(v, indices, value);
        }

        public Expr ReadMapVariableInScopeAt(Variable v, IList<Expr> indices)
        {
            if (v is GlobalVariable || v is Constant)
            {
                return Mem.Globals.ReadMap(v, indices);
            }

            // Must be a local variable
            var sf = GetCurrentStackFrame();
            return sf.Locals.ReadMap(v, indices);
        }

        private IVariableStore FindStore(Variable v)
        {
            if (v is GlobalVariable)
            {
                if (!Mem.Globals.ContainsKey(v))
                    throw new KeyNotFoundException("Variable not in globals");
                return Mem.Globals;
            }

            if (!GetCurrentStackFrame().Locals.ContainsKey(v))
                throw new KeyNotFoundException("Variable not in the locals of the current stack frame");
            return GetCurrentStackFrame().Locals;
        }

        public void DirectMapCopy(Variable dest, Variable src)
        {
            var srcStore = FindStore(src);
            var destStore = FindStore(dest);
            destStore.MapCopy(dest, src, srcStore);
        }

        public void AssignToGlobalVariable(GlobalVariable GV, Expr value)
        {
            Debug.Assert(GV.IsMutable, "Can't assign to a non mutable global!");
            if (Mem.Globals.ContainsKey(GV))
            {
                Mem.Globals[GV] = value;
                return;
            }

            throw new InvalidOperationException("Can't assign to a GlobalVariable not in memory");
        }

        public void LeaveImplementation()
        {
            if (Finished())
                throw new InvalidOperationException("Not currently in Implementation");

            Mem.PopStackFrame();
        }

        public bool Finished()
        {
            return this.TerminationType != null;
        }

        // Don't use this directly! Use the Executor.TerminateState() instead!
        public void Terminate(ITerminationType tt)
        {
            Debug.Assert(tt != null, "ITerminationType cannot be null");
            this.TerminationType = tt;

            (tt as dynamic).State = this; // Public interface doesn't allow state to be changed so cast to actual type so we can set.

            // FIXME: Add some checks to make sure the termination type corresponds
            // with the current instruction
        }

        public Expr GetGlobalVariableExpr(Variable GV)
        {
            if (GV is GlobalVariable || GV is Constant)
            {
                if (Mem.Globals.ContainsKey(GV))
                {
                    return Mem.Globals[GV];
                }
            }

            return null;
        }
    }
}

