//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    namespace Solver
    {
        public class ConstraintIndependenceSolver : ISolverImpl
        {
            ISolverImpl UnderlyingSolver;
            ConstraintIndepenceSolverStatistics InternalStatistics;
            private bool Interrupted = false;
            private Stopwatch ConstraintSetReductionTimer;

            public ConstraintIndependenceSolver(ISolverImpl underlyingSolver)
            {
                this.UnderlyingSolver = underlyingSolver;
                ConstraintSetReductionTimer = new Stopwatch();
                InternalStatistics.Reset();
            }

            public void Interrupt()
            {
                Interrupted = true;
                UnderlyingSolver.Interrupt();
            }

            public IQueryResult ComputeSatisfiability(Query query)
            {
                Interrupted = false;

                ConstraintSetReductionTimer.Start();

                HashSet<SymbolicVariable> usedVariables = new HashSet<SymbolicVariable>(query.QueryExpr.UsedVariables);
                HashSet<Function> usedUinterpretedFunctions = new HashSet<Function>(query.QueryExpr.UsedUninterpretedFunctions);


                // Compute a new constraint set that only contains relevant contraints
                HashSet<Constraint> relevantConstraints = new HashSet<Constraint>();
                bool changed = false;
                IConstraintManager reducedConstraints = null;
                do
                {
                    changed = false;
                    foreach (var constraint in query.Constraints.Constraints)
                    {
                        if (Interrupted)
                        {
                            Console.WriteLine("WARNING: ConstraintIndependenceSolver interrupted!");
                            ConstraintSetReductionTimer.Stop();
                            return new SimpleQueryResult(Result.UNKNOWN);
                        }

                        if (relevantConstraints.Contains(constraint))
                        {
                            // We've already added this constraint
                            continue;
                        }

                        if (constraint.UsedVariables.Overlaps( usedVariables ) || 
                            constraint.UsedUninterpretedFunctions.Overlaps( usedUinterpretedFunctions ))
                        {
                            // This constraint is relevant so we should pass it to
                            // the underlying solver. We also need to add the variables
                            // it uses to the usedVariables set we are maintaining so that
                            // transitively propagate the usedVariables
                            relevantConstraints.Add(constraint);
                            usedVariables.UnionWith(constraint.UsedVariables);
                            usedUinterpretedFunctions.UnionWith(constraint.UsedUninterpretedFunctions);
                            changed = true;
                        }
                    }
                } while (changed);

                // Make the new IConstraintManager
                reducedConstraints = query.Constraints.GetSubSet(relevantConstraints);

                Debug.Assert(reducedConstraints.Count <= query.Constraints.Count);
                // Update statistics
                if (reducedConstraints.Count == query.Constraints.Count)
                {
                    ++InternalStatistics.ConstraintSetsLeftUnchanged;
                }
                else
                {
                    ++InternalStatistics.ConstraintSetsReduced;
                }
                ConstraintSetReductionTimer.Stop();


                // FIXME: We should wrap the returned IQueryResult object because the client may ask
                // for the assignment to variables which we removed.
                var reducedQuery = new Query(reducedConstraints, query.QueryExpr);
                return UnderlyingSolver.ComputeSatisfiability(reducedQuery);
            }

            public void SetTimeout(int seconds)
            {
                // We assume that this solver is fast and any delay
                // is due to the underlying solver
                UnderlyingSolver.SetTimeout(seconds);
            }

            public void Dispose()
            {
                UnderlyingSolver.Dispose();
            }

            public ISolverImplStatistics Statistics
            {
                get
                {
                    InternalStatistics.UnderlyingSolverStats = UnderlyingSolver.Statistics;
                    InternalStatistics.TimeUsedToComputeReducedConstraintSet = ConstraintSetReductionTimer.Elapsed;
                    return InternalStatistics; // Return a copy
                }
            }
        }

        struct ConstraintIndepenceSolverStatistics : ISolverImplStatistics
        {
            public int ConstraintSetsReduced;
            public int ConstraintSetsLeftUnchanged;
            public ISolverImplStatistics UnderlyingSolverStats;
            public TimeSpan TimeUsedToComputeReducedConstraintSet;

            public void Reset()
            {
                ConstraintSetsReduced = 0;
                ConstraintSetsLeftUnchanged = 0;
                UnderlyingSolverStats = null;
                TimeUsedToComputeReducedConstraintSet = TimeSpan.Zero;
            }

            public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
            {
                double total = ( ConstraintSetsReduced + ConstraintSetsLeftUnchanged );
                double reduceP = 100 * ( (float) ConstraintSetsReduced ) /total;
                double sameP = 100 * ( (float) ConstraintSetsLeftUnchanged) /total;


                TW.WriteLine("{0}:", this.GetType().ToString());
                TW.Indent += 1;
                TW.WriteLine("constraint_sets_reduced: {0} #({1}%)", ConstraintSetsReduced, reduceP);
                TW.WriteLine("constraint_sets_left_unchanged: {0} #({1}%)", ConstraintSetsLeftUnchanged, sameP);
                TW.WriteLine("constraint_set_reduction_time: {0}", TimeUsedToComputeReducedConstraintSet.TotalSeconds);
                TW.WriteLine("underlying_solver:");
                TW.Indent += 1;
                UnderlyingSolverStats.WriteAsYAML(TW);
                TW.Indent -= 2;
            }
        }
    }
}

