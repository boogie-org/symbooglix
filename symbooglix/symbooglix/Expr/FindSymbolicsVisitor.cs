using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.Linq;
using System.Diagnostics;

namespace symbooglix
{
    public class FindSymbolicsVisitor : StandardVisitor
    {
        public List<IdentifierExpr> symbolics;
        public FindSymbolicsVisitor()
        {
            symbolics = new List<IdentifierExpr>();
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            Debug.Assert(node != null);

            if (node.Decl is SymbolicVariable)
            {
                Debug.Assert(node == ( node.Decl as SymbolicVariable ).expr, "Different instances for IdentiferExpr");
                symbolics.Add(node);
            }
            return node;
        }
    }
}

