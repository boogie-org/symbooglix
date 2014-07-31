using System;
using System.Diagnostics;

namespace Symbooglix
{
    namespace Solver
    {
        // This simple solver calls on a ISolverImpl to do the work
        public class SimpleSolver : ISolver
        {
            protected Stopwatch Timer;

            public ISolverImpl SolverImpl
            {
                get;
                private set;
            }

            public SimpleSolver(ISolverImpl solverImpl)
            {
                this.SolverImpl = solverImpl;
                Statistics = new SolverStats();
                Timer = new Stopwatch();
            }

            public void SetConstraints(ConstraintManager cm)
            {
                SolverImpl.SetConstraints(cm);
            }

            public void SetTimeout(int seconds)
            {
                SolverImpl.SetTimeout(seconds);
            }

            public Result IsQuerySat(Microsoft.Boogie.Expr query, out IAssignment assignment)
            {
                Timer.Start();

                var result = SolverImpl.ComputeSatisfiability(query, true);
                assignment = result.Item2;
                Debug.Assert(assignment != null, "Assignment object cannot be null");

                Timer.Stop();
                UpdateStatistics(result);
                return result.Item1;
            }

            public Result IsQuerySat(Microsoft.Boogie.Expr query)
            {
                Timer.Start();

                var result = SolverImpl.ComputeSatisfiability(query, false);

                Timer.Stop();
                UpdateStatistics(result);
                return result.Item1;
            }

            public Result IsNotQuerySat(Microsoft.Boogie.Expr query, out IAssignment assignment)
            {
                Timer.Start();

                var result = SolverImpl.ComputeSatisfiability(Microsoft.Boogie.Expr.Not(query), true);
                assignment = result.Item2;
                Debug.Assert(assignment != null, "Assignment object cannot be null");

                Timer.Stop();
                UpdateStatistics(result);
                return result.Item1;
            }

            public Result IsNotQuerySat(Microsoft.Boogie.Expr query)
            {
                Timer.Start();

                var result = SolverImpl.ComputeSatisfiability(Microsoft.Boogie.Expr.Not(query), false);

                Timer.Stop();
                UpdateStatistics(result);
                return result.Item1;
            }

            public void Dispose()
            {
                SolverImpl.Dispose();
            }

            private void UpdateStatistics(Tuple<Result, IAssignment> result)
            {
                Statistics.TotalRunTime = Timer.Elapsed;
                Statistics.Increment(result.Item1);
            }

            public SolverStats Statistics
            {
                get;
                private set;
            }
        }
    }
}

