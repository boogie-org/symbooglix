using System;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Boogie;

namespace Symbooglix
{
    public class VariableMapRewriter : Duplicator
    {
        private ExecutionState state;
        private HashSet<Variable> boundVariables;
        public bool ReplaceGlobalsOnly
        {
            get;
            set;
        }

        // If an IdentifierExpr is visited this mapping can be
        // used to change the replacement expression (normally the expr associated
        // with the key) to the expression associated with the Value.
        //
        // This is useful for procedures which have different argument variable instances
        // than the associated implementation, despite there being no good reason for this!
        // Damn you Boogie!!
        // FIXME: Fix boogie to remove this stupid requirement!
        public Dictionary<Variable,Variable> preReplacementReMap;

        public VariableMapRewriter(ExecutionState e)
        {
            this.state = e;
            boundVariables = new HashSet<Variable>();
            preReplacementReMap = new Dictionary<Variable,Variable>();
            this.ReplaceGlobalsOnly = false;
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

            // Don't remap this because this internal to this class
            if (boundVariables.Contains(node.Decl))
            {
                // Variable is bound in the expression so don't replace
                Debug.WriteLine("Variable '" + node.Decl + "' is bound, skipping");
                return base.VisitIdentifierExpr(node);
            }


            if (node.Decl is SymbolicVariable)
            {
                // In the Expr given to us by the executor we shouldn't ever has
                // IdentifierExpr containing Symbolics in because they aren't
                // in the original program
                throw new InvalidOperationException();
            }

            // Do a remappingif necessary
            // FIXME: This sucks. Fix boogie instead!
            Variable V = null;
            if (preReplacementReMap.ContainsKey(node.Decl))
                V = preReplacementReMap[node.Decl];
            else
                V = node.Decl;

            // Not a symbolic so we should try rewriting it.
            Expr e = null;
            if (ReplaceGlobalsOnly)
            {
                e = state.GetGlobalVariableExpr(V);
                if (e == null)
                {
                    // Not a global variable so leave alone
                    return base.VisitIdentifierExpr(node);
                }
            }
            else
            {
                e = state.getInScopeVariableExpr(V);

                if (e == null)
                    throw new NullReferenceException("Identifier " + V + " is not is scope");
            }

            // We remove the IdentifierExpr entirely and replace it
            // with the expression that represents this variable
            // currently.
            return e;
        }

        // FIXME: We should not duplicate literals either
    }
}

