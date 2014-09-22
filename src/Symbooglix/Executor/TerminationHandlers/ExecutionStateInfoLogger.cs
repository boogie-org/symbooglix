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

    public class ExecutionStateConstraintLogger : ExecutionStateInfoLogger
    {
        public ExecutionStateConstraintLogger(string directory) : base(directory)
        {
        }

        protected override void DoTask(Executor e, ExecutionState State)
        {
            string terminatationType = State.TerminationType.GetType().ToString();
            using (var SW = new StreamWriter(Path.Combine(Directory,State.Id + "-" + terminatationType + ".smt2")))
            {
                var outputFile = new SMTLIBQueryPrinter(SW, true);

                // FIXME: This **all** needs to be refactored. The solvers do something very similar
                foreach (var constraint in State.Constraints.ConstraintExprs)
                {
                    outputFile.AddDeclarations(constraint);
                }

                outputFile.PrintFunctionDeclarations();
                outputFile.PrintVariableDeclarations();

                foreach (var constraint in State.Constraints.Constraints)
                {
                    outputFile.PrintCommentLine("Origin : " + constraint.Origin.ToString());
                    outputFile.PrintAssert(constraint.Condition);
                }

                // FIXME: The last constraint from the execution state is missing!

                outputFile.PrintCheckSat();
                outputFile.PrintExit();
            }
        }
    }
}

