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
using System.Runtime.CompilerServices;
using Microsoft.Boogie;
using System.Diagnostics;

namespace Symbooglix
{
    // FIXME: Add tests for this

    /// <summary>
    /// Duplication verifier. This exists purely for debugging Expr duplication
    /// </summary>
    public class DuplicationVerifier
    {
        HashSet<Expr> SeenNodes;
        bool IgnoreDuplicateConstants;
        bool IgnoreDuplicateSymbolics;
        public DuplicationVerifier(bool ignoreDuplicateConstansts, bool ignoreDuplicateSymbolics)
        {
            SeenNodes = new HashSet<Expr>(new ExprReferenceCompare());
            IgnoreDuplicateConstants = ignoreDuplicateConstansts;
            IgnoreDuplicateSymbolics = ignoreDuplicateSymbolics;
        }

        public List<Expr> CheckDuplication(Expr original, Expr duplicated)
        {
            var nodeStack = new Stack<Expr>();
            var duplicates = new List<Expr>();

            // Collect node's in original's tree in DFS pre-order
            nodeStack.Push(original);
            while (nodeStack.Count > 0)
            {
                var node = nodeStack.Pop();
                SeenNodes.Add(node);

                for (int index = node.GetNumberOfChildren() -1 ; index >= 0 ; --index)
                {
                    nodeStack.Push(node.GetChild(index));
                }
            }

            nodeStack.Clear();


            // Walk through duplicated's nodes (DFS pre-order) checking to see if we've seen them beofre
            nodeStack.Push(duplicated);
            while (nodeStack.Count > 0)
            {
                var node = nodeStack.Pop();

                if (SeenNodes.Contains(node))
                {
                    if (IgnoreDuplicateConstants && node is LiteralExpr)
                    {
                        // Don't record it
                    }
                    else if (IgnoreDuplicateSymbolics && node is IdentifierExpr && ( node as IdentifierExpr ).Decl is SymbolicVariable)
                    {
                        // Don't record duplicate symbolic
                    }
                    else
                    {
                        duplicates.Add(node);
                        Debug.Print("Found duplicate!");
                    }
                }

                for (int index = node.GetNumberOfChildren() -1 ; index >= 0 ; --index)
                {
                    nodeStack.Push(node.GetChild(index));
                }
            }
            return duplicates;
        }
    }

    class ExprReferenceCompare : IEqualityComparer<Expr>
    {
        public bool Equals(Expr x, Expr y)
        {
            return Object.ReferenceEquals(x, y);
        }

        public int GetHashCode(Expr obj)
        {
            return RuntimeHelpers.GetHashCode(obj);
        }
    }
}

