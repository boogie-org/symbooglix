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
using System.IO;
using System.Collections.Generic;

namespace Symbooglix
{
    public class ExecutionTreeLogger : AbstractExecutorFileLogger
    {
        bool AnnotateWithContextChanges = false;
        List<Tuple<ExecutionTreeNode,ExecutionTreeNode>> ContextChanges=null;


        public ExecutionTreeLogger(bool annotateWithContextChanges=false)
        {
            this.AnnotateWithContextChanges = annotateWithContextChanges;

            if (this.AnnotateWithContextChanges)
                ContextChanges = new List<Tuple<ExecutionTreeNode, ExecutionTreeNode>>();
        }

        public override void Connect(Executor e)
        {
            e.ExecutorTerminated += HandleExecutorTerminated;

            if (AnnotateWithContextChanges)
                e.ContextChanged += HandleContextChanged;
        }

        void HandleContextChanged (object sender, Executor.ContextChangeEventArgs e)
        {
            ContextChanges.Add(Tuple.Create(e.Previous.TreeNode, e.Next.TreeNode));
        }

        void HandleExecutorTerminated(object sender, Executor.ExecutorTerminatedArgs e)
        {
            var path = Path.Combine(this.Directory, "execution_tree.dot");
            var executor = (Executor) sender;

            if (executor.TreeRoot == null)
            {
                Console.Error.WriteLine("Can't create {0}, tree root is null", path.ToString());
                return;
            }

            using (var SW = new StreamWriter(path))
            {
                ExecutionTreePrinter etp = null;

                if (AnnotateWithContextChanges)
                    etp = new ExecutionTreePrinterWithContextChanges(executor.TreeRoot, 2, this.ContextChanges);
                else
                    etp = new ExecutionTreePrinter(executor.TreeRoot);
                etp.Print(SW);
            }
        }

        public override void Disconnect(Executor e)
        {
            e.ExecutorTerminated -= HandleExecutorTerminated;

            if (AnnotateWithContextChanges)
                e.ContextChanged -= HandleContextChanged;
        }
    }

    class ExecutionTreePrinterWithContextChanges : ExecutionTreePrinter
    {
        IList<Tuple<ExecutionTreeNode,ExecutionTreeNode>> ContextChanges;
        public ExecutionTreePrinterWithContextChanges(ExecutionTreeNode root, int indent, IList<Tuple<ExecutionTreeNode,ExecutionTreeNode>> contextChanges ) : base(root, indent)
        {
            this.ContextChanges = contextChanges;
        }

        protected override void PrintAdditionalEdges(TextWriter TW, ExecutionTreeNode root)
        {
            int counter = 0;
            TW.WriteLine("/* Context changes */");
            foreach (var pair in this.ContextChanges)
            {
                TW.WriteLine("{0} -> {1} [color=red, label=\"{2}\"];", GetNodeID(pair.Item1), GetNodeID(pair.Item2), counter);
                ++counter;
            }
        }
    }
}

