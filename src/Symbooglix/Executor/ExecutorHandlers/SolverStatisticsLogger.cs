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
            var path = Path.Combine(this.Directory, "solver_statistics.yml");
            Console.WriteLine("Logging solver statistics to {0}", path);
            using (var SW = new StreamWriter(path))
            {
                using (var ITW = new System.CodeDom.Compiler.IndentedTextWriter(SW, "  "))
                {
                    ITW.WriteLine("solver_stats:");
                    ITW.Indent += 1;
                    Solver.Statistics.WriteAsYAML(ITW);
                    ITW.Indent -= 1;


                    SW.WriteLine("solver_impl_stats:");
                    ITW.Indent += 1;
                    Solver.SolverImpl.Statistics.WriteAsYAML(ITW);
                    ITW.Indent -= 1;
                }
            }
        }

        public override void Disconnect(Executor e)
        {
            e.ExecutorTerminated -= HandleExecutorTerminated;
        }
    }
}

