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
            private bool Interrupted = false;

            public ConstraintIndependenceSolver(ISolverImpl underlyingSolver)
            {
                this.UnderlyingSolver = underlyingSolver;
                InternalStatistics.Reset();
            }

            public void SetConstraints(IConstraintManager constraints)
            {
                // Don't pass these on to the underlying solver.
                OriginalConstraints = constraints;
            }

            public void Interrupt()
            {
                Interrupted = true;
                UnderlyingSolver.Interrupt();
            }

            public Tuple<Result, IAssignment> ComputeSatisfiability(Expr queryExpr, bool computeAssignment)
            {
                Interrupted = false;
                if (computeAssignment)
                {
                    // We may prevent the underlying solver from seeing some variables
                    // so it won't be able to provide an assignment to them.
                    //
                    // We need to handle this in some way.
                    throw new NotImplementedException();
                }

                HashSet<SymbolicVariable> usedVariables = new HashSet<SymbolicVariable>();
                HashSet<Function> usedUinterpretedFunctions = new HashSet<Function>();
                var FSV = new FindSymbolicsVisitor(usedVariables);
                var FUFV = new FindUinterpretedFunctionsVisitor(usedUinterpretedFunctions);
                FSV.Visit(queryExpr);
                FUFV.Visit(queryExpr);


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
                        if (Interrupted)
                        {
                            Console.WriteLine("WARNING: ConstraintIndependenceSolver interrupted!");
                            return new Tuple<Result, IAssignment>(Result.UNKNOWN, null);
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
                    return InternalStatistics; // Return a copy
                }
            }
        }

        struct ConstraintIndepenceSolverStatistics : ISolverImplStatistics
        {
            public int ConstraintSetsReduced;
            public int ConstraintSetsLeftUnchanged;
            public ISolverImplStatistics UnderlyingSolverStats;

            public void Reset()
            {
                ConstraintSetsReduced = 0;
                ConstraintSetsLeftUnchanged = 0;
                UnderlyingSolverStats = null;
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
                TW.WriteLine("underlying_solver:");
                TW.Indent += 1;
                UnderlyingSolverStats.WriteAsYAML(TW);
                TW.Indent -= 2;
            }
        }
    }
}

