using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.Diagnostics;

namespace symbooglix
{
    public class FindFunctionsVisitor : StandardVisitor
    {
        public ICollection<Function> foundFuctions;

        // Internal container
        public FindFunctionsVisitor()
        {
            foundFuctions = new List<Function>();
        }

        // External container
        public FindFunctionsVisitor(ICollection<Function> externalContainer)
        {
            foundFuctions = externalContainer;
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (!(node.Fun is FunctionCall))
                return base.VisitNAryExpr(node);

            var FC = node.Fun as FunctionCall;

            // Don't collect SMTLIBv2 functions
            if (QKeyValue.FindStringAttribute(FC.Func.Attributes, "bvbuiltin") != null)
                return base.VisitNAryExpr(node);

            foundFuctions.Add(FC.Func);
            return base.VisitNAryExpr(node); // Make sure we visit children
        }
    }
}

