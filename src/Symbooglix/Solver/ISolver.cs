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
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    namespace Solver
    {
        // FIXME: The client has know way of knowing if a timeout was hit!
        public enum Result {SAT, UNSAT, UNKNOWN};


        public interface IQueryResult
        {
            Result Satisfiability { get; }

            // null if not available
            IAssignment GetAssignment();
            IUnsatCore GetUnsatCore();
        }

        public interface IBranchSatisfiabilityResult
        {
            Result TrueBranch { get; }
            Result FalseBranch { get; }
        }

        // This solver interface is what the Executor uses and thus
        // is designed around the needs of the Executor rather than the solver
        public interface ISolver : IDisposable
        {
            void SetTimeout(int seconds);

            IBranchSatisfiabilityResult CheckBranchSatisfiability(IConstraintManager constraints, Constraint trueExpr, IExprBuilder builder);

            IQueryResult CheckSatisfiability(Query query);

            // Get access to the underlying implementation
            ISolverImpl SolverImpl { get; }

            // Get Solver statistics. The object
            // returned is guaranteed not to change
            // when the solver is invoked again.
            SolverStats Statistics { get; }

            // Interrupt the solver if it is running, forcing it to return an UNKNOWN result
            // FIXME: This is gross and demonstrates that the current Solver design is bad.
            // We need to rewrite the whole thing using a "Pipe and Filter" design pattern
            // where we would instead tell the pipeline engine to interrupt whatever it happening
            void Interrupt();
        }

        public interface IAssignment
        {
            Microsoft.Boogie.LiteralExpr GetAssignment(SymbolicVariable SV);
        }

        public interface IUnsatCore
        {
            // TODO
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

        // Simplest implementation
        public class SimpleQueryResult : IQueryResult
        {
            public SimpleQueryResult(Result r)
            {
                Satisfiability = r;
            }

            public IAssignment GetAssignment()
            {
                throw new NotSupportedException();
            }

            public IUnsatCore GetUnsatCore()
            {
                throw new NotSupportedException();
            }

            public Result Satisfiability
            {
                get;
                private set;
            }
        }
    }
}

