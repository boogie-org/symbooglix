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
            IConstraintManager OriginalConstraints;
            IConstraintManager ReducedConstraints;
            ConstraintIndepenceSolverStatistics InternalStatistics;

            public ConstraintIndependenceSolver(ISolverImpl underlyingSolver)
            {
                this.UnderlyingSolver = underlyingSolver;
                InternalStatistics = new ConstraintIndepenceSolverStatistics(null);
            }

            public void SetConstraints(IConstraintManager constraints)
            {
                // Don't pass these on to the underlying solver.
                OriginalConstraints = constraints;
            }

            public Tuple<Result, IAssignment> ComputeSatisfiability(Expr queryExpr, bool computeAssignment)
            {
                if (computeAssignment)
                {
                    // We may prevent the underlying solver from seeing some variables
                    // so it won't be able to provide an assignment to them.
                    //
                    // We need to handle this in some way.
                    throw new NotImplementedException();
                }

                HashSet<SymbolicVariable> usedVariables = new HashSet<SymbolicVariable>();
                var FSV = new FindSymbolicsVisitor(usedVariables);
                FSV.Visit(queryExpr);

                // FIXME: We might get called again with the negation of the previous query.
                // we SHOULD OPTIMISE FOR THIS CASE (no recomputation needed, the used varaibles and hence
                // relevant constraints won't have changed)

                // Compute a new constraint set that only contains relevant contraints
                HashSet<Constraint> relevantConstraints = new HashSet<Constraint>();
                bool changed = false;
                do
                {
                    changed = false;
                    foreach (var constraint in OriginalConstraints.Constraints)
                    {
                        if (relevantConstraints.Contains(constraint))
                        {
                            // We've already added this constraint
                            continue;
                        }

                        if (constraint.UsedVariables.Overlaps( usedVariables ))
                        {
                            // This constraint is relevant so we should pass it to
                            // the underlying solver. We also need to add the variables
                            // it uses to the usedVariables set we are maintaining so that
                            // transitively propagate the usedVariables
                            relevantConstraints.Add(constraint);
                            usedVariables.UnionWith(constraint.UsedVariables);
                            changed = true;
                        }
                    }
                } while (changed);

                // Make the new IConstraintManager
                ReducedConstraints = OriginalConstraints.GetSubSet(relevantConstraints);

                Debug.Assert(ReducedConstraints.Count <= OriginalConstraints.Count);
                // Update statistics
                if (ReducedConstraints.Count == OriginalConstraints.Count)
                {
                    ++InternalStatistics.ConstraintSetsLeftUnchanged;
                }
                else
                {
                    ++InternalStatistics.ConstraintSetsReduced;
                }

                UnderlyingSolver.SetConstraints(ReducedConstraints);
                return UnderlyingSolver.ComputeSatisfiability(queryExpr, computeAssignment);
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
                    return InternalStatistics.DeepClone();
                }
            }
        }

        class ConstraintIndepenceSolverStatistics : ISolverImplStatistics
        {
            public int ConstraintSetsReduced = 0;
            public int ConstraintSetsLeftUnchanged = 0;
            public ISolverImplStatistics UnderlyingSolverStats;

            public ConstraintIndepenceSolverStatistics(ISolverImplStatistics underlyingStats)
            {
                UnderlyingSolverStats = underlyingStats;
            }

            public void Dump(System.IO.TextWriter TW)
            {
                double total = ( ConstraintSetsReduced + ConstraintSetsLeftUnchanged );
                double reduceP = 100 * ( (float) ConstraintSetsReduced ) /total;
                double sameP = 100 * ( (float) ConstraintSetsLeftUnchanged) /total;
                TW.WriteLine("[ConstraintIndependenceSolver]");
                TW.WriteLine("ConstraintSetsReduced: {0} ({1}%)", ConstraintSetsReduced, reduceP);
                TW.WriteLine("ConstraintSetsLeftUnchanged: {0} ({1}%)", ConstraintSetsLeftUnchanged, sameP);
                TW.WriteLine("");
                TW.WriteLine("Underlying solver stats:");
                UnderlyingSolverStats.Dump(TW);
            }

            public ISolverImplStatistics DeepClone()
            {
                return (ISolverImplStatistics) this.MemberwiseClone();
            }
        }
    }
}

