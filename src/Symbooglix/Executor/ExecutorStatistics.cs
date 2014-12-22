using System;
using System.Diagnostics;
using System.IO;

namespace Symbooglix
{
    public struct ExecutorStatistics : Util.IDumpable, Util.IYAMLWriter
    {
        public TimeSpan RunTime;
        public TimeSpan PrepareTime;
        public int InstructionsExecuted;
        public Executor.ExecutorTerminationType TerminationType;

        public void Reset()
        {
            this.RunTime = TimeSpan.Zero;
            this.PrepareTime = TimeSpan.Zero;
            this.InstructionsExecuted = 0;
            TerminationType = Executor.ExecutorTerminationType.UNKNOWN;
        }

        public void Dump(TextWriter TW)
        {
            TW.WriteLine("Prepare time: {0} seconds", PrepareTime.TotalSeconds);
            TW.WriteLine("Run Time: {0} seconds", RunTime.TotalSeconds);
            TW.WriteLine("# Instructions executed: {0}", InstructionsExecuted);
            TW.WriteLine("Executor termination type: {0}", TerminationType.ToString());
        }

        public override string ToString()
        {
            string result;
            using (var SW = new StringWriter())
            {
                Dump(SW);
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
            TW.WriteLine("termination_type: \"{0}\"", TerminationType.ToString());
        }
    }
}

