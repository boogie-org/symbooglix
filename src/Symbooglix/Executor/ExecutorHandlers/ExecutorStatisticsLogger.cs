using System;
using System.IO;

namespace Symbooglix
{
    public class ExecutorStatisticsLogger : AbstractExecutorFileLogger
    {
        public ExecutorStatisticsLogger()
        {
        }

        public override void Connect(Executor e)
        {
            e.ExecutorTerminated += HandleExecutorTerminated;
        }

        void HandleExecutorTerminated(object sender, Executor.ExecutorTerminatedArgs e)
        {
            var executor = sender as Executor;
            using (var SW = new StreamWriter(Path.Combine(Directory, "executor_statistics.txt")))
            {
                executor.Statistics.Dump(SW);
            }
        }
        public override void Disconnect(Executor e)
        {
            e.ExecutorTerminated -= HandleExecutorTerminated;
        }
    }
}

