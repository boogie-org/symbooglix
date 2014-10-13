using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public class ExecutionTreeNode
    {
        public readonly ExecutionTreeNode Parent;
        public readonly ProgramLocation CreatedAt;
        public readonly ExecutionState State; // Should this be a weak reference to allow GC?
        public readonly int Depth;
        private List<ExecutionTreeNode> Children;

        public ExecutionTreeNode(ExecutionState self, ExecutionTreeNode parent, ProgramLocation createdAt)
        {
            Debug.Assert(self != null, "self cannot be null!");
            this.State = self;
            if (parent == null)
                this.Parent = null;
            else
            {
                this.Parent = parent;

                // Add this as a child of the parent
                this.Parent.AddChild(this);
            }

            this.Depth = self.ExplicitBranchDepth;

            this.CreatedAt = createdAt;
            Children = new List<ExecutionTreeNode>(); // Should we lazily create this?
        }

        public ExecutionTreeNode GetChild(int index)
        {
            return Children[index];
        }

        public int ChildrenCount
        {
            get { return Children.Count; }
        }

        public void AddChild(ExecutionTreeNode node)
        {
            Debug.Assert(node != null, "Child cannot be null");
            Debug.Assert(node != this, "Cannot have cycles");
            Children.Add(node);
        }

        public override string ToString()
        {
            return string.Format ("[{0}.{1}]", State.Id, this.Depth);
        }
    }
}

