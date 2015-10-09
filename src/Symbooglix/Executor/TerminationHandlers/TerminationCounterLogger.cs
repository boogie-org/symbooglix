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
using System.CodeDom.Compiler;
using System.Text;

namespace Symbooglix
{
    public class TerminationCounterLogger : AbstractExecutorFileLogger
    {
        private TerminationCounter TCounter;

        public TerminationCounterLogger(TerminationCounter.CountType countType)
        {
            TCounter = new TerminationCounter(countType);
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
            StringBuilder fileName = new StringBuilder("termination_counters");

            if (TCounter.TheCountType != TerminationCounter.CountType.ONLY_NON_SPECULATIVE)
            {
                fileName.AppendFormat("_{0}", TCounter.TheCountType.ToString());
            }

            // Write GNUPlot data
            string path = Path.Combine(Directory, fileName.ToString() + ".txt");
            Console.WriteLine("Writing termination counts to {0}", path);
            using (var SW = new StreamWriter(path))
            {
                TCounter.WriteAsGnuPlotData(SW);
            }

            path = Path.Combine(Directory, fileName.ToString() + ".yml");
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

