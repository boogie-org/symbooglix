using System;
using System.IO;

namespace Symbooglix
{
    public class ExecutionTreeLogger : IExecutorEventHandler
    {
        string Directory;

        public ExecutionTreeLogger(string directory)
        {
            this.Directory = directory;
        }

        public void Connect(Executor e)
        {
            e.ExecutorTerminated += HandleExecutorTerminated;
        }

        void HandleExecutorTerminated(object sender, Executor.ExecutorTerminatedArgs e)
        {
            var path = Path.Combine(this.Directory, "execution_tree.dot");
            var executor = (Executor) sender;
            using (var SW = new StreamWriter(path))
            {
                var etp = new ExecutionTreePrinter(executor.TreeRoot);
                etp.Print(SW);
            }
        }

        public void Disconnect(Executor e)
        {
            e.ExecutorTerminated -= HandleExecutorTerminated;
        }
    }
}

