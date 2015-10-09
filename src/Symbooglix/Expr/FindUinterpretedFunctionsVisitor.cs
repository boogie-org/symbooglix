//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.Diagnostics;

namespace Symbooglix
{
    public class FindUinterpretedFunctionsVisitor : ReadOnlyVisitor
    {
        public ICollection<Function> foundFuctions;

        // Internal container
        public FindUinterpretedFunctionsVisitor()
        {
            foundFuctions = new List<Function>();
        }

        // External container
        public FindUinterpretedFunctionsVisitor(ICollection<Function> externalContainer)
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

            // Don't collect other builtins
            if (QKeyValue.FindStringAttribute(FC.Func.Attributes, "builtin") != null)
                return base.VisitNAryExpr(node);

            foundFuctions.Add(FC.Func);
            return base.VisitNAryExpr(node); // Make sure we visit children
        }
    }
}

