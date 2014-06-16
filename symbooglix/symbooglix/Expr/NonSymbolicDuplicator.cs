using System;
using Microsoft.Boogie;
using System.Diagnostics;

namespace symbooglix
{
    /// <summary>
    /// This duplicates Expr accept the identifier expr attached to symbolics
    /// </summary>
    public class NonSymbolicDuplicator : Duplicator
    {
        public NonSymbolicDuplicator()
        {
        }

        public override Expr VisitIdentifierExpr (IdentifierExpr node)
        {
            if (node.Decl is SymbolicVariable)
            {
                Debug.Assert(node == ( node.Decl as SymbolicVariable ).expr, "Mismatched Symbolic IdentifierExpr");
                return node;
            }
            else
                return base.VisitIdentifierExpr (node);
        }
    }
}

