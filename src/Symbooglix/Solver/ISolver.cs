using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    namespace Solver
    {
        // FIXME: The client has know way of knowing if a timeout was hit!
        public enum Result {SAT, UNSAT, UNKNOWN};

        // This solver interface is what the Executor uses and thus
        // is designed around the needs of the Executor rather than the solver
        public interface ISolver : IDisposable
        {
            void SetConstraints(ConstraintManager cm);

            void SetTimeout(int seconds);

            // Given the constraints is the query expression satisfiable
            // \return True iff sat
            // if sat the assignment will be set to an assignment object
            //
            // If another query is made the previously received assignment object may be
            // invalid.
            Result IsQuerySat(Microsoft.Boogie.Expr query, out IAssignment assignment);

            // Same as above but no assignment is requested
            Result IsQuerySat(Microsoft.Boogie.Expr query);

            // Given the constraints is the negation of the query expression satisfiable
            // \return True iff sat
            // if sat the assignment will be set to an assignment object
            //
            // If another query is made the previously received assignment object may be
            // invalid.
            Result IsNotQuerySat(Microsoft.Boogie.Expr query, out IAssignment assignment);

            // Same as above but no assignment is requested
            Result IsNotQuerySat(Microsoft.Boogie.Expr query);

            // Get access to the underlying implementation
            ISolverImpl SolverImpl { get; }

            // Get Solver statistics. The object
            // returned is guaranteed not to change
            // when the solver is invoked again.
            SolverStats Statistics { get; }
        }

        public interface IAssignment
        {
            Microsoft.Boogie.LiteralExpr GetAssignment(SymbolicVariable SV);
        }

        public class SolverStats : Util.IDeepClone<SolverStats>, Util.IDumpable
        {
            // Stats on number of queries
            public int SatQueries { get; internal set; }
            public int UnsatQueries { get; internal set; }
            public int UnknownQueries { get; internal set; }
            public int TotalQueries
            {
                get { return SatQueries + UnsatQueries + UnknownQueries; }
            }

            public SolverStats()
            {
                SatQueries = 0;
                UnsatQueries = 0;
                UnknownQueries = 0;
                TotalRunTime = TimeSpan.Zero;
            }

            // Stats on runtime
            public TimeSpan TotalRunTime { get; internal set;}

            // Helper
            public void Increment(Result result)
            {
                switch (result)
                {
                    case Result.SAT:
                        ++SatQueries;
                        break;
                    case Result.UNSAT:
                        ++UnsatQueries;
                        break;
                    case Result.UNKNOWN:
                        ++UnknownQueries;
                        break;
                    default:
                        throw new InvalidOperationException("Result of type " + result.ToString() + " not handled");
                }
            }

            public void Dump(System.IO.TextWriter TW)
            {
                TW.WriteLine("Sat queries:{0}", SatQueries);
                TW.WriteLine("Unsat queries:{0}", UnsatQueries);
                TW.WriteLine("Unknown queries:{0}", UnknownQueries);
                TW.WriteLine("Total queries:{0}", TotalQueries);
                TW.WriteLine("Total run time:{0} seconds", TotalRunTime.TotalSeconds);
            }

            public override string ToString()
            {
                string result;
                using (var SW = new System.IO.StringWriter())
                {
                    Dump(SW);
                    result = SW.ToString();
                }
                return result;
            }

            // Clients need to call this if they want an instance
            // not is guaranteed not to change when the solver is
            // invoked again.
            public SolverStats DeepClone()
            {
                // This should be fine because all the types are value types
                return this.MemberwiseClone() as SolverStats;
            }
        }

        public class InvalidSolverTimeoutException : Exception
        {

        }
    }
}

