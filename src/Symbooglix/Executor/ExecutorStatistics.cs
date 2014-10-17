using System;
using System.Diagnostics;
using System.IO;

namespace Symbooglix
{
    public class ExecutorStatistics : Util.IDeepClone<ExecutorStatistics>, Util.IDumpable
    {
        public TimeSpan RunTime;
        public TimeSpan PrepareTime;
        public int InstructionsExecuted;

        public ExecutorStatistics()
        {
            Reset();
        }

        public void Reset()
        {
            this.RunTime = TimeSpan.Zero;
            this.PrepareTime = TimeSpan.Zero;
            this.InstructionsExecuted = 0;
        }

        public ExecutorStatistics DeepClone()
        {
            return (ExecutorStatistics) this.MemberwiseClone();
        }

        public void Dump(TextWriter TW)
        {
            TW.WriteLine("Prepare time: {0} seconds", PrepareTime.TotalSeconds);
            TW.WriteLine("Run Time: {0} seconds", RunTime.TotalSeconds);
            TW.WriteLine("# Instructions executed: {0}", InstructionsExecuted);
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
    }
}

