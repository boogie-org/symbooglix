using System;
using System.IO;
using System.CodeDom.Compiler;

namespace Symbooglix
{
    public class TerminationCounterLogger : AbstractExecutorFileLogger
    {
        private TerminationCounter TCounter;

        public TerminationCounterLogger()
        {
            TCounter = new TerminationCounter();
        }

        public override void Connect(Executor e)
        {
            TCounter.Connect(e);
            e.ExecutorTerminated += handleExecutorTerminated;
        }

        public override void Disconnect(Executor e)
        {
            TCounter.Disconnect(e);
            e.ExecutorTerminated -= handleExecutorTerminated;
        }

        private void handleExecutorTerminated(Object executor, Executor.ExecutorTerminatedArgs args)
        {
            // Write GNUPlot data
            string path = Path.Combine(Directory, "termination_counters.txt");
            Console.WriteLine("Writing termination counts to {0}", path);
            using (var SW = new StreamWriter(path))
            {
                TCounter.WriteAsGnuPlotData(SW);
            }

            path = Path.Combine(Directory, "termination_counters.yml");
            Console.WriteLine("Writing termination counts to {0}", path);

            // It is necessary to use to "using" blocks because IndentedTextWriter.Dispose()
            // does not seem to call Dispose() on the underlying stream
            using (var SW = new StreamWriter(path))
            {
                using (var ITT = new IndentedTextWriter(SW, " "))
                {
                    TCounter.WriteAsYAML(ITT);
                }
            }
        }
    }
}

