using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Linq;
using System.Diagnostics;

namespace symbooglix
{
    public class ExecutionState
    {
        public Memory mem;
        private bool started = false;
        public List<SymbolicVariable> symbolics;

        // FIXME: Loads axioms and types

        // FIXME: Add Path Constraints container

        // FIXME: Add something to track program counter in an elegant way that handles block commands

        public ExecutionState()
        {
            mem = new Memory();
            symbolics = new List<SymbolicVariable>();
        }

        public bool dumpStackTrace()
        {
            // TODO
            return true;
        }

        public bool dumpState()
        {
            return mem.dump();
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

            if (v is GlobalVariable)
            {
                GlobalVariable g = (GlobalVariable)v;
                // If not in stackframe look through globals
                if (mem.globals.ContainsKey(g))
                {
                    return mem.globals [g];
                }
            }

            return null;
        }

        public bool isInScopeVariable(Variable v)
        {
            if (getCurrentStackFrame().locals.ContainsKey(v))
                return true;

            if (v is GlobalVariable)
            {
                GlobalVariable g = (GlobalVariable)v;
                if (mem.globals.ContainsKey(g))
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
            if (getCurrentStackFrame().locals.ContainsKey(v))
            {
                getCurrentStackFrame().locals [v] = value;
                return;
            }


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

            Debug.WriteLine(getCurrentStackFrame().ToString());
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

