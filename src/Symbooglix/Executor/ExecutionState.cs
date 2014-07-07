using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace Symbooglix
{
    public class ExecutionState : Util.IDeepClone<ExecutionState>
    {
        public Memory Mem;
        private bool Started = false;
        private bool TerminatedEarly = false;
        public List<SymbolicVariable> Symbolics;
        public ConstraintManager Constraints;
        public int Id
        {
            get;
            private set;
        }
        private static int NewId = 0;

        public ExecutionState()
        {
            Mem = new Memory();
            Symbolics = new List<SymbolicVariable>();
            Constraints = new ConstraintManager();
            Id = NewId++;
        }

        public ExecutionState DeepClone()
        {
            ExecutionState other = (ExecutionState) this.MemberwiseClone();
            other.Mem = this.Mem.DeepClone();

            other.Symbolics = new List<SymbolicVariable>();
            foreach (SymbolicVariable s in this.Symbolics)
            {
                other.Symbolics.Add(s);
            }

            other.Id = NewId++;

            other.Constraints = this.Constraints.DeepClone();
            return other;
        }

        public bool DumpStackTrace()
        {
            // TODO
            return true;
        }

        public void DumpState()
        {
            Console.Write("State {0} :", this.Id);
            if (TerminatedEarly)
                Console.WriteLine("Terminated early");
            else if (Finished())
                Console.WriteLine("Finished");
            else
                Console.WriteLine("Running");

            Console.WriteLine(Mem);
            Console.WriteLine(Constraints);
        }
       
        public StackFrame GetCurrentStackFrame()
        {
            return Mem.Stack.Last();
        }

        public Block GetCurrentBlock()
        {
            return GetCurrentStackFrame().CurrentBlock;
        }

        public void EnterImplementation(Implementation impl)
        {
            Started = true;
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
            if (AssignToVariableInStack(GetCurrentStackFrame(), v, value))
                return;

            if (v is GlobalVariable)
            {
                var g = v as GlobalVariable;
                if (Mem.Globals.ContainsKey(g))
                {
                    Mem.Globals [g] = value;
                    return;
                }
            }

            throw new InvalidOperationException("Cannot assign to variable not in scope.");

        }

        public void LeaveImplementation()
        {
            if (Finished())
                throw new InvalidOperationException("Not currently in Implementation");

            Mem.PopStackFrame();
        }

        public bool Finished()
        {
            if (HasTerminatedEarly() || TerminatedSuccessfuly())
                return true;
            else
                return false;
        }

        public void MarkAsTerminatedEarly()
        {
            this.TerminatedEarly = true;
        }

        public bool HasTerminatedEarly()
        {
            return TerminatedEarly;
        }

        public bool TerminatedSuccessfuly()
        {
            if (Started && !TerminatedEarly && ( Mem.Stack.Count == 0 ))
                return true;
            else
                return false;
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

