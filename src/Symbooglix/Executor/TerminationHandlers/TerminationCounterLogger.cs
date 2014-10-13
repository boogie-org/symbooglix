using System;
using System.IO;

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
            string path = Path.Combine(Directory, "termination_counters.txt");
            Console.WriteLine("Writing termination counts to {0}", path);
            using (var SW = new StreamWriter(path))
            {
                TCounter.WriteGnuPlotData(SW);
            }
        }
    }
}

