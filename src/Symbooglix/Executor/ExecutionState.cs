using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace Symbooglix
{
    public class ExecutionState : Util.IDeepClone<ExecutionState>
    {
        public Memory mem;
        private bool started = false;
        private bool terminatedEarly = false;
        public List<SymbolicVariable> symbolics;
        public ConstraintManager cm;
        public int id
        {
            get;
            private set;
        }
        private static int newId = 0;

        public ExecutionState()
        {
            mem = new Memory();
            symbolics = new List<SymbolicVariable>();
            cm = new ConstraintManager();
            id = newId++;
        }

        public ExecutionState DeepClone()
        {
            ExecutionState other = (ExecutionState) this.MemberwiseClone();
            other.mem = this.mem.DeepClone();

            other.symbolics = new List<SymbolicVariable>();
            foreach (SymbolicVariable s in this.symbolics)
            {
                other.symbolics.Add(s);
            }

            other.id = newId++;

            other.cm = this.cm.DeepClone();
            return other;
        }

        public bool dumpStackTrace()
        {
            // TODO
            return true;
        }

        public void dumpState()
        {
            Console.Write("State {0} :", this.id);
            if (terminatedEarly)
                Console.WriteLine("Terminated early");
            else if (finished())
                Console.WriteLine("Finished");
            else
                Console.WriteLine("Running");

            Console.WriteLine(mem);
            Console.WriteLine(cm);
        }
       
        public StackFrame getCurrentStackFrame()
        {
            return mem.Stack.Last();
        }

        public Block getCurrentBlock()
        {
            return getCurrentStackFrame().CurrentBlock;
        }

        public void enterProcedure(Implementation p)
        {
            started = true;
            StackFrame s = new StackFrame(p);
            mem.Stack.Add(s);
        }

        // Returns variable Expr if in scope, otherwise
        // return null
        public Expr getInScopeVariableExpr(Variable v)
        {
            // Only the current stackframe is in scope
            if (getCurrentStackFrame().Locals.ContainsKey(v))
            {
                return getCurrentStackFrame().Locals [v];
            }

            if (v is GlobalVariable || v is Constant)
            {
                // If not in stackframe look through globals
                if (mem.Globals.ContainsKey(v))
                {
                    return mem.Globals[v];
                }
            }

            return null;
        }

        public KeyValuePair<Variable,Expr> getInScopeVariableAndExprByName(string name)
        {
            var local = ( from pair in getCurrentStackFrame().Locals
                         where pair.Key.Name == name
                         select pair );
            if (local.Count() != 0)
            {
                Debug.Assert(local.Count() == 1);
                return local.First();
            }

            var global = ( from pair in mem.Globals
                          where pair.Key.Name == name
                          select pair );

            Debug.Assert(global.Count() == 1, "The requested global was not found");
            var kp = global.First();
            return new KeyValuePair<Variable,Expr>( (Variable) kp.Key, kp.Value);
        }

  
        public bool assignToVariableInStack(StackFrame s, Variable v, Expr value)
        {
            Debug.Assert(mem.Stack.Contains(s));

            if (s.Locals.ContainsKey(v))
            {
                s.Locals [v] = value;
                return true;
            }

            return false;

        }

        public bool isInScopeVariable(Variable v)
        {
            if (getCurrentStackFrame().Locals.ContainsKey(v))
                return true;

            if (v is GlobalVariable || v is Constant)
            {
                if (mem.Globals.ContainsKey(v))
                    return true;
            }

            return false;
        }

        public bool isInScopeVariable(IdentifierExpr i)
        {
            return isInScopeVariable(i.Decl);
        }

        public void assignToVariableInScope(Variable v, Expr value)
        {
            if (assignToVariableInStack(getCurrentStackFrame(), v, value))
                return;

            if (v is GlobalVariable)
            {
                var g = v as GlobalVariable;
                if (mem.Globals.ContainsKey(g))
                {
                    mem.Globals [g] = value;
                    return;
                }
            }

            throw new InvalidOperationException("Cannot assign to variable not in scope.");

        }

        public void leaveProcedure()
        {
            if (finished())
                throw new InvalidOperationException("Not currently in procedure");

            mem.PopStackFrame();
        }

        public bool finished()
        {
            if (HasTerminatedEarly() || TerminatedSuccessfuly())
                return true;
            else
                return false;
        }

        public void MarkAsTerminatedEarly()
        {
            this.terminatedEarly = true;
        }

        public bool HasTerminatedEarly()
        {
            return terminatedEarly;
        }

        public bool TerminatedSuccessfuly()
        {
            if (started && !terminatedEarly && ( mem.Stack.Count == 0 ))
                return true;
            else
                return false;
        }

        public Expr GetGlobalVariableExpr(Variable GV)
        {
            if (GV is GlobalVariable || GV is Constant)
            {
                if (mem.Globals.ContainsKey(GV))
                {
                    return mem.Globals[GV];
                }
            }

            return null;
        }
    }
}

