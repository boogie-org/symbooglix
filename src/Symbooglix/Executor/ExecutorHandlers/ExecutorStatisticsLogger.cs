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

            // It is necessary to use to "using" blocks because IndentedTextWriter.Dispose()
            // does not seem to call Dispose() on the underlying stream
            using (var SW = new StreamWriter(Path.Combine(Directory, "executor_statistics.yml")))
            {
                using (var ITT = new IndentedTextWriter(SW, " "))
                {
                    executor.Statistics.WriteAsYAML(ITT);
                }
            }
        }
        public override void Disconnect(Executor e)
        {
            e.ExecutorTerminated -= HandleExecutorTerminated;
        }
    }
}

