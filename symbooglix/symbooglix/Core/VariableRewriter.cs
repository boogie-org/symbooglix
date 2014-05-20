using System;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Boogie;

namespace symbooglix
{
    // This class duplicates on Expr like the Duplicator
    // but it optionally allows Variables to be rewritten (i.e. substituted)
    // with another Variable.
    // 
    // The initial use case for this is rewriting requires statements attached
    // to procedures to refer to the implementation's arguments instead of
    // the procedure's which confusingly are different instances.
    public class VariableRewriter : Duplicator
    {
        public Dictionary<Variable,Variable> VariableMap;
        public VariableRewriter()
        {
            VariableMap = new Dictionary<Variable,Variable>();
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            IdentifierExpr copy = (IdentifierExpr) base.VisitIdentifierExpr(node);

            if (VariableMap.ContainsKey(node.Decl))
            {
                copy.Decl = VariableMap[node.Decl];
                Debug.WriteLine("Rewriting {0} => {1}", node.Decl, copy.Decl);
            }

            return copy;
        }
    }
}

