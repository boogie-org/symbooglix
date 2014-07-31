using System;
using System.Diagnostics;

namespace Symbooglix
{
    namespace Solver
    {
        // This simple solver calls on a ISolverImpl to do the work
        public class SimpleSolver : ISolver
        {
            public ISolverImpl SolverImpl
            {
                get;
                private set;
            }

            public SimpleSolver(ISolverImpl solverImpl)
            {
                this.SolverImpl = solverImpl;
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
                var result = SolverImpl.ComputeSatisfiability(query, true);
                assignment = result.Item2;
                Debug.Assert(assignment != null, "Assignment object cannot be null");
                return result.Item1;
            }

            public Result IsQuerySat(Microsoft.Boogie.Expr query)
            {
                var result = SolverImpl.ComputeSatisfiability(query, false);
                return result.Item1;
            }

            public Result IsNotQuerySat(Microsoft.Boogie.Expr query, out IAssignment assignment)
            {
                var result = SolverImpl.ComputeSatisfiability(Microsoft.Boogie.Expr.Not(query), true);
                assignment = result.Item2;
                Debug.Assert(assignment != null, "Assignment object cannot be null");
                return result.Item1;
            }

            public Result IsNotQuerySat(Microsoft.Boogie.Expr query)
            {
                var result = SolverImpl.ComputeSatisfiability(Microsoft.Boogie.Expr.Not(query), false);
                return result.Item1;
            }

            public void Dispose()
            {
                SolverImpl.Dispose();
            }
        }
    }
}

