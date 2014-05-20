using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.Linq;
using System.Diagnostics;

namespace symbooglix
{
    /// <summary>
    /// Yuck! I need a better way to do this.
    /// This visitor relies on the invariant that in expr
    /// stored by symbooglix the only identifier expressions refer
    /// to symbolic variables. Does this even work for constants?
    /// </summary>
    public class FindSymbolicsVisitor : StandardVisitor
    {
        public List<IdentifierExpr> symbolics;
        public ExecutionState State;
        public FindSymbolicsVisitor(ExecutionState State)
        {
            symbolics = new List<IdentifierExpr>();
            this.State = State;
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            Debug.Assert(node != null);
            Debug.Assert(State.symbolics.Where(sv => sv.expr == node).Count() == 1);
            symbolics.Add(node);
            return node;
        }
    }
}

