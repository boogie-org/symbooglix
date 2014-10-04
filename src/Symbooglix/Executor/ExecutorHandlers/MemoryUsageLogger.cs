using System;
using System.IO;
using System.Threading.Tasks;
using System.Threading;
using System.Diagnostics;

namespace Symbooglix
{
    public class MemoryUsageLogger : IExecutorEventHandler
    {
        private string Directory;
        private bool Run = true;
        private Task MemoryLoggingTask;
        public MemoryUsageLogger(string directory)
        {
            this.Directory = directory;
        }

        protected void handleStart(Object executor, Executor.ExecutorStartedArgs args)
        {
            MemoryLoggingTask = Task.Factory.StartNew( () =>
            {
                using (var SW = new StreamWriter(Path.Combine(Directory, "memory_use.txt")))
                {
                    var stopWatch = new Stopwatch();
                    Console.WriteLine("Starting memory log");
                    SW.WriteLine("# < seconds >, < Memory usage (MB)>");
                    stopWatch.Start();
                    while (this.Run)
                    {
                        var estimatedBytes = System.GC.GetTotalMemory(/*forceFullCollection=*/false);
                        SW.WriteLine("{0}, {1}", stopWatch.Elapsed.TotalSeconds, ( (double) estimatedBytes)/( 2 << 20));
                        Thread.Sleep(1000);
                    }
                    Console.WriteLine("Stopping memory log");
                }

            }, TaskCreationOptions.LongRunning);
        }

        protected void handleTerminate(Object executor, Executor.ExecutorTerminatedArgs args)
        {
            Run = false;
            MemoryLoggingTask.Wait();
        }

        public void Connect(Executor e)
        {
            e.ExecutorStarted += handleStart;
            e.ExecutorTerminated += handleTerminate;
        }


        public void Disconnect(Executor e)
        {
            e.ExecutorStarted -= handleStart;
            e.ExecutorTerminated -= handleTerminate;
        }
    }
}

