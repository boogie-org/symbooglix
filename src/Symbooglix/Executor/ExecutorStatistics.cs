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
using System.Diagnostics;
using System.IO;

namespace Symbooglix
{
    public struct ExecutorStatistics : Util.IYAMLWriter
    {
        public TimeSpan RunTime;
        public TimeSpan PrepareTime;
        public int InstructionsExecuted;
        public int ForkCount;
        public Executor.ExecutorTerminationType TerminationType;

        public void Reset()
        {
            this.RunTime = TimeSpan.Zero;
            this.PrepareTime = TimeSpan.Zero;
            this.InstructionsExecuted = 0;
            this.ForkCount = 0;
            TerminationType = Executor.ExecutorTerminationType.UNKNOWN;
        }

        public override string ToString()
        {
            string result;
            using (var SW = new StringWriter())
            {
                using (var ITW = new System.CodeDom.Compiler.IndentedTextWriter(SW))
                {
                    WriteAsYAML(ITW);
                }
                result = SW.ToString();
            }
            return result;
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            TW.WriteLine("#Executor statistics as YAML. Times are in seconds");
            TW.WriteLine("prepare_time: {0}", PrepareTime.TotalSeconds);
            TW.WriteLine("run_time: {0}", RunTime.TotalSeconds);
            TW.WriteLine("instructions_executed: {0}", InstructionsExecuted);
            TW.WriteLine("num_forks: {0}", ForkCount);
            TW.WriteLine("termination_type: \"{0}\"", TerminationType.ToString());
        }
    }
}

