using System;
using Microsoft.Boogie;

namespace symbooglix
{
    public class VariableMapRewriter : StandardVisitor
    {
        private ExecutionState state;
        public VariableMapRewriter(ExecutionState e)
        {
            this.state = e;
        }

        public override Expr VisitIdentifierExpr (IdentifierExpr node)
        {
            // Look for variables and expand them to what they map to
            // so that the map only every contains expressions involving constants
            // and symbolics

            // Check our symbolics, we don't need to rewrite those
            // FIXME: Should we be doing this check, it might get slow?
            foreach (SymbolicVariable s in state.symbolics)
            {
                if (s.expr == node)
                    return (Expr) base.Visit(node);
            }

            // Not a symbolic so we should try rewriting it.
            Expr e = state.getInScopeVariableExpr(node.Decl);

            if (e == null)
                throw new NullReferenceException("Identifier is not is scope");

            // We remove the IdentifierExpr entirely and replace it
            // with the expression that represents this variable
            // currently.
            // FIXME: Do we need to duplicate here?
            return e;
        }
    }
}

