using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;

namespace symbooglix
{
    public class DFSPostOrderTraverser : Traverser, IErrorSink
    {
        public DFSPostOrderTraverser(IExprVisitor visitor) : base(visitor)
        {

        }

        // So we pass by value
        struct ExprNodeInfo
        {
            public Expr node;
            public Expr parent;
            public int childNumber;
        }

        public override Expr Traverse(Expr root)
        {
            // The approach we use is to compute pre-order (Right-left visiting of children)
            // DFS traversal. We also record the parent of each node so we can do tree rewritting
            // if the visitor requests this.
            //
            // Once we have this list we can walk it backwards to do DFS post-order (left-right visiting of children)
            // traversal.
            if (root == null)
                throw new ArgumentNullException("root cannot be null");

            var preOrderRL = new List<ExprNodeInfo>();

            // Do DFS pre-order (RL)
            var queue = new Stack<ExprNodeInfo>();
            ExprNodeInfo info;
            info.parent = null;
            info.node = root;
            info.childNumber = 0;
            queue.Push(info);

            while (queue.Count != 0)
            {
                var head = queue.Pop();
                preOrderRL.Add(head);

                // Add children in LR order to queue (when we pop we'll do RL)
                for (int index = 0; index < head.node.GetNumberOfChildren(); ++index)
                {
                    info.parent = head.node;
                    info.node = head.node.GetChild(index);
                    info.childNumber = index;
                    queue.Push(info);
                }
            }

            // Phew! We can now post order traversal. Just walk the list backwards
            Expr rootToReturn = root;
            for (int index = preOrderRL.Count - 1; index >= 0; --index)
            {
                ExprNodeInfo nodeToVisitInfo = preOrderRL[index];
                Expr replacementNode = Visit(nodeToVisitInfo.node);

                if (replacementNode != nodeToVisitInfo.node)
                {
                    // We are mutating the tree
                    Debug.WriteLine("Mutating tree: '{0}' => '{1}'", nodeToVisitInfo.node, replacementNode);

                    // Root node has no parent
                    if (nodeToVisitInfo.parent == null)
                    {
                        rootToReturn = replacementNode;
                    }
                    else
                    {
                        nodeToVisitInfo.parent.SetChild(nodeToVisitInfo.childNumber, replacementNode);
                    }
                }
            }

            #if DEBUG
            // Do type checking
            var TC = new TypecheckingContext(this);
            rootToReturn.Typecheck(TC);
            #endif

            return rootToReturn;
        }

        public void Error(IToken tok, string msg)
        {
            throw new Exception("TypeChecking error:" + msg);
        }

    }
}

