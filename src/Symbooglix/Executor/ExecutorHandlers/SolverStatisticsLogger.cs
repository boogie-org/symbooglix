using System;
using System.IO;

namespace Symbooglix
{
    public class SolverStatisticsLogger : AbstractExecutorFileLogger
    {
        private Solver.ISolver Solver;
        public SolverStatisticsLogger(Solver.ISolver solver)
        {
            this.Solver = solver;
        }

        public override void Connect(Executor e)
        {
            e.ExecutorTerminated += HandleExecutorTerminated;
        }

        void HandleExecutorTerminated(object sender, Executor.ExecutorTerminatedArgs e)
        {
            var path = Path.Combine(this.Directory, "solver_statistics.txt");
            Console.WriteLine("Logging solver statistics to {0}", path);
            using (var SW = new StreamWriter(path))
            {
                SW.WriteLine("[Solver statistics]");
                Solver.Statistics.Dump(SW);

                SW.WriteLine("");
                SW.WriteLine("");

                SW.WriteLine("[SolverImpl statistics]");
                Solver.SolverImpl.Statistics.Dump(SW);
            }
        }

        public override void Disconnect(Executor e)
        {
            e.ExecutorTerminated -= HandleExecutorTerminated;
        }
    }
}

