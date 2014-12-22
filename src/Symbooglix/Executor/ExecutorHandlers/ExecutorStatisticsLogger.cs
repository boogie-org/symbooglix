using System;
using System.IO;
using System.CodeDom.Compiler;

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
            using (var SW = new IndentedTextWriter(new StreamWriter(Path.Combine(Directory, "executor_statistics.yml")), "  "))
            {
                executor.Statistics.WriteAsYAML(SW);
            }
        }
        public override void Disconnect(Executor e)
        {
            e.ExecutorTerminated -= HandleExecutorTerminated;
        }
    }
}

