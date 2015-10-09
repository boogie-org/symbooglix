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
using System.Diagnostics;
using System.Threading.Tasks;

namespace Symbooglix
{
    namespace Solver
    {
        // This simple solver calls on a ISolverImpl to do the work
        public class SimpleSolver : ISolver
        {
            private bool TryInterupt = false;
            protected Stopwatch Timer;
            private SolverStats InternalStatistics;
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

            public void SetTimeout(int seconds)
            {
                SolverImpl.SetTimeout(seconds);
            }

            class SimpleBranchSatsifiabilityResult : IBranchSatisfiabilityResult
            {
                public SimpleBranchSatsifiabilityResult(Result trueBranch, Result falseBranch)
                {
                    this.TrueBranch = trueBranch;
                    this.FalseBranch = falseBranch;
                }

                public Result TrueBranch
                {
                    get;
                    private set;
                }

                public Result FalseBranch
                {
                    get;
                    private set;
                }
            };

            public IBranchSatisfiabilityResult CheckBranchSatisfiability(IConstraintManager constraints, Constraint trueExpr, IExprBuilder builder)
            {
                // Note: We implicitly assume that the constraints are satisfiable
                TryInterupt = false;
                IQueryResult falseBranchResult = null;
                IQueryResult trueBranchResult = null;
                try
                {
                    Timer.Start();
                    // Fast path: trueExpr is constant
                    var trueExprAsLit = ExprUtil.AsLiteral(trueExpr.Condition);
                    if (trueExprAsLit != null)
                    {
                        if (!trueExprAsLit.isBool)
                            throw new ExprTypeCheckException("trueExpr must be of boolean type");

                        if (trueExprAsLit.asBool)
                            return new SimpleBranchSatsifiabilityResult(Result.SAT, Result.UNSAT);
                        else
                            return new SimpleBranchSatsifiabilityResult(Result.UNSAT, Result.SAT);
                    }

                    // Slow path: Invoke solver

                    // First see if it's possible for the false branch to be feasible
                    // ∃ X constraints(X) ∧ ¬ condition(X)
                    var query = new Solver.Query(constraints, trueExpr);
                    falseBranchResult =  InternalComputeSatisfiability(query.WithNegatedQueryExpr(builder));
                    var falseBranch = falseBranchResult.Satisfiability;


                    var trueBranch = Result.UNKNOWN;
                    // Only invoke solver again if necessary
                    if (falseBranch == Result.UNSAT)
                    {
                        // This actually implies that
                        //
                        // ∀X : C(X) → Q(X)
                        // That is if the constraints are satisfiable then
                        // the query expr is always true. Because we've been
                        // checking constraints as we go we already know C(X) is satisfiable
                        trueBranch = Result.SAT;
                    }
                    else
                    {
                        if (TryInterupt)
                        {
                            // Don't do next solver call
                            Console.Error.WriteLine("WARNING: Tried to kill solver during CheckBranchSatisfiability()");
                            return new SimpleBranchSatsifiabilityResult(Result.UNKNOWN, falseBranch);
                        }

                        // Now see if it's possible for execution to continue past the assertion
                        // ∃ X constraints(X) ∧ condition(X)
                        trueBranchResult = InternalComputeSatisfiability(query);
                        trueBranch = trueBranchResult.Satisfiability;
                    }

                    return new SimpleBranchSatsifiabilityResult(trueBranch, falseBranch);
                }
                finally
                {
                    Timer.Stop();
                    if (falseBranchResult != null)
                        UpdateStatistics(falseBranchResult);

                    if (trueBranchResult != null)
                        UpdateStatistics(trueBranchResult);
                }
            }

            protected IQueryResult InternalComputeSatisfiability(Query query)
            {
                // Check for a few things that we can quick give an answer for
                // otherwise call the real solver

                if (ExprUtil.IsTrue(query.QueryExpr.Condition))
                    return new SimpleQueryResult(Result.SAT);

                if (ExprUtil.IsFalse(query.QueryExpr.Condition))
                    return new SimpleQueryResult(Result.UNSAT);

                // If queryExpr is already in the constraint set then the result
                // is satisfiable
                if (query.Constraints.Contains(query.QueryExpr))
                    return new SimpleQueryResult(Result.SAT);

                return SolverImpl.ComputeSatisfiability(query);
            }
           

            public IQueryResult CheckSatisfiability(Query query)
            {
                // FIXME: We need to enforce the timeout here but doing so isn't possible with the current design.
                // If we implement a timeout then we need away to create a new solverImplementation when the timeout hits
                // because we'll need a way to throw away the old solver (we have no idea what states its in).
                /// We can't do that right now, we need to introduce
                // an ISolverImplFactory that we take so we can create new solver implementations whenever it's necessary.
                Timer.Start();

                var result = InternalComputeSatisfiability(query);

                Timer.Stop();
                UpdateStatistics(result);
                return result;
            }

            public void Interrupt()
            {
                this.TryInterupt = true;
                SolverImpl.Interrupt();
            }

            public void Dispose()
            {
                SolverImpl.Dispose();
            }

            private void UpdateStatistics(IQueryResult result)
            {
                Debug.Assert(!Timer.IsRunning, "Timer should not been running whilst statistics are being updated");
                InternalStatistics.TotalRunTime = Timer.Elapsed;
                InternalStatistics.Increment(result.Satisfiability);
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

