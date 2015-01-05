using System;
using System.Diagnostics;
using System.Threading.Tasks;

namespace Symbooglix
{
    namespace Solver
    {
        // This simple solver calls on a ISolverImpl to do the work
        public class SimpleSolver : ISolver
        {
            protected Stopwatch Timer;
            private SolverStats InternalStatistics;
            private int Timeout = -1; // No timeout by default
            public ISolverImpl SolverImpl
            {
                get;
                private set;
            }

            public SimpleSolver(ISolverImpl solverImpl)
            {
                this.SolverImpl = solverImpl;
                InternalStatistics.Reset();
                Timer = new Stopwatch();
            }

            public void SetConstraints(IConstraintManager cm)
            {
                SolverImpl.SetConstraints(cm);
            }

            public void SetTimeout(int seconds)
            {
                SolverImpl.SetTimeout(seconds);
                this.Timeout = seconds * 1000;
            }

            private Tuple<Result, IAssignment> CallImplementation(Microsoft.Boogie.Expr queryExpr, bool getAssignment)
            {
                // FIXME: We need to enforce the timeout here but doing so isn't possible with the current design.
                // If we implement a timeout then we need away to create a new solverImplementation when the timeout hits
                // because we'll need a way to throw away the old solver (we have no idea what states its in).
                /// We can't do that right now, we need to introduce
                // an ISolverImplFactory that we take so we can create new solver implementations whenever it's necessary.

                //Console.WriteLine("Starting solver");
                var result = SolverImpl.ComputeSatisfiability(queryExpr, getAssignment);
                //Console.WriteLine("Finished solver");
                return result;
            }

            public Result IsQuerySat(Microsoft.Boogie.Expr query, out IAssignment assignment)
            {
                Timer.Start();

                var result = CallImplementation(query, true);
                assignment = result.Item2;
                Debug.Assert(assignment != null, "Assignment object cannot be null");

                Timer.Stop();
                UpdateStatistics(result);
                return result.Item1;
            }

            public Result IsQuerySat(Microsoft.Boogie.Expr query)
            {
                Timer.Start();

                var result = CallImplementation(query, false);

                Timer.Stop();
                UpdateStatistics(result);
                return result.Item1;
            }

            public Result IsNotQuerySat(Microsoft.Boogie.Expr query, out IAssignment assignment)
            {
                Timer.Start();

                var result = CallImplementation(Microsoft.Boogie.Expr.Not(query), true);
                assignment = result.Item2;
                Debug.Assert(assignment != null, "Assignment object cannot be null");

                Timer.Stop();
                UpdateStatistics(result);
                return result.Item1;
            }

            public Result IsNotQuerySat(Microsoft.Boogie.Expr query)
            {
                Timer.Start();

                var result = CallImplementation(Microsoft.Boogie.Expr.Not(query), false);

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
                Debug.Assert(!Timer.IsRunning, "Timer should not been running whilst statistics are being updated");
                InternalStatistics.TotalRunTime = Timer.Elapsed;
                InternalStatistics.Increment(result.Item1);
            }

            public SolverStats Statistics
            {
                // The client should get a copy that won't change
                // when the solver is invoked again.
                get
                {
                    return InternalStatistics;
                }
            }
        }
    }
}

