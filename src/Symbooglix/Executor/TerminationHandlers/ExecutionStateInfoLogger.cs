using System;
using System.Threading.Tasks;
using System.Threading;
using System.Collections.Generic;
using System.IO;

namespace Symbooglix
{
    public abstract class ExecutionStateInfoLogger : IExecutorEventHandler
    {
        protected string Directory;
        public ExecutionStateInfoLogger(string directory)
        {
            this.Directory = directory;
        }

        private List<Task> ScheduledTasks = new List<Task>();

        private void handle(Object executor, Executor.ExecutionStateEventArgs args)
        {
            lock (ScheduledTasks)
            {
                var task = Task.Factory.StartNew(() =>
                {
                    DoTask(executor as Executor, args.State);
                });
                ScheduledTasks.Add(task);
            }
        }

        public void Connect(Executor e)
        {
            e.StateTerminated += handle;
        }

        public void Disconnect(Executor e)
        {
            e.StateTerminated -= handle;
        }

        protected abstract void DoTask(Executor e, ExecutionState State);

        // Yuck! Is there a better way to do this that ensures that our Tasks
        // always finish before the program is allowed to Terminate?
        public void Wait()
        {
            Task.WaitAll(ScheduledTasks.ToArray());
        }
    }
}

