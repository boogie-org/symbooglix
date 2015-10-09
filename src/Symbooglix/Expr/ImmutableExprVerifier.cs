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

namespace Symbooglix
{
    // FIXME: Write tests for this
    public class ImmutableExprVerifier
    {
        public HashSet<Expr> NonImmutableNodes;
        public ImmutableExprVerifier()
        {
            NonImmutableNodes = new HashSet<Expr>();
        }

        public void Reset()
        {
            NonImmutableNodes.Clear();
        }

        public void Visit(Expr root)
        {
            var visited = new HashSet<Expr>();
            var nodeStack = new Stack<Expr>();

            // DFS pre-order
            nodeStack.Push(root);
            while (nodeStack.Count > 0)
            {
                var node = nodeStack.Pop();

                if (visited.Contains(node))
                {
                    // We've seen this before so don't go deeper
                    continue;
                }
                else
                    visited.Add(node);

                if (!node.Immutable)
                    NonImmutableNodes.Add(node);

                // Put children on the queue
                for (int index = 0; index < node.GetNumberOfChildren(); ++index)
                    nodeStack.Push(node.GetChild(index));
            }
        }
    }
}

