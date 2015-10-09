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
using Microsoft.Boogie;
using System.Diagnostics;

namespace Symbooglix
{
    /// <summary>
    /// This duplicates Expr accept the identifier expr attached to symbolics
    /// </summary>
    // TODO: Should we remove this, it's dead code now!? If were to use it should use BuilderDuplicator instead
    public class NonSymbolicDuplicator : Duplicator
    {
        public NonSymbolicDuplicator()
        {
        }

        public override Absy Visit(Absy node)
        {
            var result = base.Visit(node);

            #if DEBUG
            Debug.Assert(node is Expr);
            Debug.Assert(result is Expr);
            var dc = new DuplicationVerifier(true, true);
            var duplicates = dc.CheckDuplication(node as Expr, result as Expr);
            Debug.Assert(duplicates.Count == 0, "Duplication detected. Found " + duplicates.Count);
            #endif

            return result;
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            if (node.Decl is SymbolicVariable)
            {
                Debug.Assert(node == ( node.Decl as SymbolicVariable ).Expr, "Mismatched Symbolic IdentifierExpr");
                if (node != ( node.Decl as SymbolicVariable ).Expr)
                    throw new Exception("FIXME");
                return node;
            }
            else
                return base.VisitIdentifierExpr(node);
        }

        // FIXME: I think this is a bug in boogie. IdentifierExpr get cloned twice!
        // By also overriding this method we prevent IdentifierExpr belonging to symbolics getting cloned
        public override Expr VisitExpr(Expr node)
        {
            if (node is IdentifierExpr && (node as IdentifierExpr).Decl is SymbolicVariable)
                return (Expr) this.Visit(node); // Skip duplication
            else
                return base.VisitExpr(node); // Duplicate as normal
        }
    }
}

