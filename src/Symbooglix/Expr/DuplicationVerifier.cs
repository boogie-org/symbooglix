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

        private void GatherChildNodes(Expr node, Stack<Expr> nodeStack)
        {
            for (int index = node.GetNumberOfChildren() -1 ; index >= 0 ; --index)
            {
                nodeStack.Push(node.GetChild(index));
            }

            // Triggers on quantified expressions aren't included is "getChild()" methods, gather those if they exist
            var asQuantifierExpr = node as QuantifierExpr;
            if (asQuantifierExpr != null)
            {
                // We consider all the triggers to be direct children of the quantified expression
                Trigger trigger = asQuantifierExpr.Triggers;
                while (trigger != null)
                {
                    foreach (var triggerExpr in trigger.Tr)
                        nodeStack.Push(triggerExpr);

                    trigger = trigger.Next;
                }
            }
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
                GatherChildNodes(node, nodeStack);
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
                GatherChildNodes(node, nodeStack);
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

