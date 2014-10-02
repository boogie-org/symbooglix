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
            e.ExecutorTerminated += Wait;
        }

        public void Disconnect(Executor e)
        {
            e.StateTerminated -= handle;
            e.ExecutorTerminated -= Wait;
        }

        protected abstract void DoTask(Executor e, ExecutionState State);

        // We need a way to ensure that our tasks finish before the application
        // using this class exits because it will just exit without letting our
        // tasks finish if we don't explicitly wait. This is achieved by hooking
        // into the ExecutorTerminated event and then waiting on all the tasks we
        // have. Is there a better way to do this???
        private void Wait(Object executor, Executor.ExecutorTerminatedArgs args)
        {
            Task.WaitAll(ScheduledTasks.ToArray());
        }
    }
}

