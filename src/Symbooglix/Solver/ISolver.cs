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
            void SetConstraints(IConstraintManager cm);

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

        // This is a struct so clients always get a copy when they try to access this.
        public struct SolverStats : Util.IYAMLWriter
        {
            // Stats on number of queries
            public int SatQueries { get; internal set; }
            public int UnsatQueries { get; internal set; }
            public int UnknownQueries { get; internal set; }
            public int TotalQueries
            {
                get { return SatQueries + UnsatQueries + UnknownQueries; }
            }

            public void Reset()
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

            public void WriteAsYAML (System.CodeDom.Compiler.IndentedTextWriter TW)
            {
                TW.WriteLine("sat_queries: {0}", SatQueries);
                TW.WriteLine("unsat_queries: {0}", UnsatQueries);
                TW.WriteLine("unknown_queries: {0}", UnknownQueries);
                TW.WriteLine("total_queries: {0}", TotalQueries);
                TW.WriteLine("total_run_time: {0}", TotalRunTime.TotalSeconds);
            }

            public override string ToString()
            {
                string result;
                using (var SW = new System.IO.StringWriter())
                {
                    using (var ITW = new System.CodeDom.Compiler.IndentedTextWriter(SW))
                    {
                        WriteAsYAML(ITW);
                    }
                    result = SW.ToString();
                }
                return result;
            }
        }

        public class InvalidSolverTimeoutException : Exception
        {

        }
    }
}

