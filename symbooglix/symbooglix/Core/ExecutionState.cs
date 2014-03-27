using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace symbooglix
{
    public class ExecutionState : util.IDeepClone<ExecutionState>
    {
        public Memory mem;
        private bool started = false;
        public List<SymbolicVariable> symbolics;
        public ConstraintManager cm;
        public int id
        {
            get;
            private set;
        }
        private static int newId = 0;

        // FIXME: Loads axioms and types

        // FIXME: Add Path Constraints container

        // FIXME: Add something to track program counter in an elegant way that handles block commands

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
            Console.WriteLine(mem);
            Console.WriteLine(cm);
        }
       
        public StackFrame getCurrentStackFrame()
        {
            return mem.stack.Last();
        }

        public Block getCurrentBlock()
        {
            return getCurrentStackFrame().currentBlock;
        }

        public void enterProcedure(Implementation p)
        {
            started = true;
            StackFrame s = new StackFrame(p);
            mem.stack.Add(s);
        }

        // Returns variable Expr if in scope, otherwise
        // return null
        public Expr getInScopeVariableExpr(Variable v)
        {
            // Only the current stackframe is in scope
            if (getCurrentStackFrame().locals.ContainsKey(v))
            {
                return getCurrentStackFrame().locals [v];
            }

            if (v is GlobalVariable || v is Constant)
            {
                // If not in stackframe look through globals
                if (mem.globals.ContainsKey(v))
                {
                    return mem.globals[v];
                }
            }

            return null;
        }

        public KeyValuePair<Variable,Expr> getInScopeVariableAndExprByName(string name)
        {
            var local = ( from pair in getCurrentStackFrame().locals
                         where pair.Key.Name == name
                         select pair );
            if (local.Count() != 0)
            {
                Debug.Assert(local.Count() == 1);
                return local.First();
            }

            var global = ( from pair in mem.globals
                          where pair.Key.Name == name
                          select pair );

            Debug.Assert(global.Count() == 1, "The requested global was not found");
            var kp = global.First();
            return new KeyValuePair<Variable,Expr>( (Variable) kp.Key, kp.Value);
        }

  
        public bool assignToVariableInStack(StackFrame s, Variable v, Expr value)
        {
            Debug.Assert(mem.stack.Contains(s));

            if (s.locals.ContainsKey(v))
            {
                s.locals [v] = value;
                return true;
            }

            return false;

        }

        public bool isInScopeVariable(Variable v)
        {
            if (getCurrentStackFrame().locals.ContainsKey(v))
                return true;

            if (v is GlobalVariable || v is Constant)
            {
                if (mem.globals.ContainsKey(v))
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
                if (mem.globals.ContainsKey(g))
                {
                    mem.globals [g] = value;
                    return;
                }
            }

            throw new InvalidOperationException("Cannot assign to variable not in scope.");

        }

        public void leaveProcedure()
        {
            if (finished())
                throw new InvalidOperationException("Not currently in procedure");

            mem.popStackFrame();
        }

        public bool finished()
        {
            if (started && mem.stack.Count == 0)
                return true;
            else
                return false;
        }

    }
}

