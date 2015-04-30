using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{

    public class Constraint
    {
        public Expr Condition { get; private set;}
        public ProgramLocation Origin { get; private set;}

        // Hide the implementation of the Set
        private HashSet<SymbolicVariable> InternalUsedVariables;
        public ISet<SymbolicVariable> UsedVariables { get { return InternalUsedVariables; } }

        private HashSet<Function> InternalUsedUninterpretedFunctions;
        public ISet<Function> UsedUninterpretedFunctions { get { return InternalUsedUninterpretedFunctions; } }

        public Constraint(Expr condition)
        {
            Condition = condition;
            Debug.Assert(condition.ShallowType.IsBool, "Constraint must be a boolean expression!");
            Origin = null;
            ComputeUsedVariablesAndUninterpretedFunctions();
        }

        public Constraint(Expr condition, ProgramLocation location) : this(condition)
        {
            Debug.Assert(location != null);
            Origin = location;
            ComputeUsedVariablesAndUninterpretedFunctions();
        }

        public Constraint GetNegatedConstraint()
        {
            var that = (Constraint) this.MemberwiseClone();

            // Optimisation:
            // We don't need to recompute (or copy) the set of used UF and variables
            // for that

            // Negate the Condition
            if (!Condition.Type.IsBool)
                throw new ExprTypeCheckException("Cannot negate an expression that is not a bool");

            // FIXME: We should be using an IExprBuilder
            that.Condition = Expr.Not(this.Condition);
            return that;
        }

        private void ComputeUsedVariablesAndUninterpretedFunctions()
        {
            this.InternalUsedVariables = new HashSet<SymbolicVariable>();
            var fsv = new FindSymbolicsVisitor(this.InternalUsedVariables);
            fsv.Visit(this.Condition);

            this.InternalUsedUninterpretedFunctions = new HashSet<Function>();
            var ffv = new FindUinterpretedFunctionsVisitor(this.InternalUsedUninterpretedFunctions);
            ffv.Visit(this.Condition);
        }
    }

    class ConstraintInHashSetCompare : IEqualityComparer<Constraint>
    {
        public bool Equals(Constraint x, Constraint y)
        {
            // Potentially slow comparision
            return ExprUtil.StructurallyEqual(x.Condition, y.Condition);
        }

        public int GetHashCode(Constraint obj)
        {
            return obj.Condition.GetHashCode();
        }
    }
}

