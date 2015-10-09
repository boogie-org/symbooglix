//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using System.IO;
using System.Threading.Tasks;
using System.Threading;
using System.Diagnostics;

namespace Symbooglix
{
    public class MemoryUsageLogger : AbstractExecutorFileLogger
    {
        private bool Run = true;
        private Task MemoryLoggingTask;

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
                        SW.Flush();
                        Thread.Sleep(1000);
                    }
                    Console.WriteLine("Stopping memory log");
                }

            }, TaskCreationOptions.LongRunning);
        }

        protected void handleTerminate(Object executor, Executor.ExecutorTerminatedArgs args)
        {
            // There is a bug here where the Thread.Sleep() doesn't wake whilst System.Environment.Exit() is being called
            Run = false;
            if (MemoryLoggingTask != null)
                MemoryLoggingTask.Wait();
        }

        public override void Connect(Executor e)
        {
            e.ExecutorStarted += handleStart;
            e.ExecutorTerminated += handleTerminate;
        }


        public override void Disconnect(Executor e)
        {
            e.ExecutorStarted -= handleStart;
            e.ExecutorTerminated -= handleTerminate;
        }
    }
}

