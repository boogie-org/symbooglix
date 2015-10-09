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

namespace Symbooglix
{
    public class ExecutorInfoLogger : AbstractExecutorFileLogger
    {
        public ExecutorInfoLogger()
        {
        }

        public override void Connect(Executor e)
        {
            e.ExecutorTerminated += HandleExecutorTerminated;
        }

        void HandleExecutorTerminated(object sender, Executor.ExecutorTerminatedArgs e)
        {
            var executor = sender as Executor;

            // It is necessary to use two "using" blocks because IndentedTextWriter.Dispose()
            // does not seem to call Dispose() on the underlying stream
            using (var SW = new StreamWriter(Path.Combine(Directory, "executor_info.yml")))
            {
                using (var ITT = new IndentedTextWriter(SW, "  "))
                {
                    ITT.WriteLine("# vim: set sw=2 ts=2 softtabstop=2:");
                    ITT.WriteLine("# Times are in seconds");
                    executor.WriteAsYAML(ITT);
                }
            }
        }
        public override void Disconnect(Executor e)
        {
            e.ExecutorTerminated -= HandleExecutorTerminated;
        }
    }
}

