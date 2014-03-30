using System;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Boogie;

namespace symbooglix
{
    public class VariableMapRewriter : Duplicator
    {
        private ExecutionState state;
        private HashSet<Variable> boundVariables;
        public VariableMapRewriter(ExecutionState e)
        {
            this.state = e;
            boundVariables = new HashSet<Variable>();
        }

        // To support forall and exists we need to keep to track of their quantified
        // variables so we don't try to substitute them
        public override BinderExpr VisitBinderExpr(BinderExpr node)
        {
            boundVariables.UnionWith(node.Dummies);
            BinderExpr toReturn = base.VisitBinderExpr(node);
            boundVariables.RemoveWhere(e => node.Dummies.Contains(e));
            return toReturn;
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            // Look for variables and expand them to what they map to
            // so that the map only every contains expressions involving constants
            // and symbolics

            if (boundVariables.Contains(node.Decl))
            {
                // Variable is bound in the expression so don't replace
                Debug.WriteLine("Variable '" + node.Decl + "' is bound, skipping");
                return base.VisitIdentifierExpr(node);
            }

            // Check our symbolics, we don't need to rewrite those
            // FIXME: Should we be doing this check, it might get slow?
            foreach (SymbolicVariable s in state.symbolics)
            {
                if (s.expr == node)
                    return (Expr) s.expr; // Don't need to duplicate these
            }

            // Not a symbolic so we should try rewriting it.
            Expr e = state.getInScopeVariableExpr(node.Decl);

            if (e == null)
                throw new NullReferenceException("Identifier " + node.Decl + " is not is scope");

            // We remove the IdentifierExpr entirely and replace it
            // with the expression that represents this variable
            // currently.
            return e;
        }

        // FIXME: We should not duplicate literals either
    }
}

