using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Microsoft.Boogie;
using System.IO;

namespace Symbooglix
{
    public interface IConstraintManager : Util.IDeepClone<IConstraintManager>, Util.IDumpable
    {
        int Count { get; }
        IEnumerable<Expr> ConstraintExprs{ get; }
        IEnumerable<Constraint> Constraints { get; }
        void AddConstraint(Expr e, ProgramLocation location);

        /// <summary>
        /// Returns
        /// </summary>
        /// <returns>A new constraint manager containing a subset of the constraints if "subset" is a true
        /// subset otherwise it returns itself
        /// </returns>
        /// <param name="subset">This should be a subset of the constraints in the IConstraintManager
        /// </param>
        IConstraintManager GetSubSet(ISet<Constraint> subset);
    }

    public class ConstraintManager : IConstraintManager
    {
        // FIXME: We are doing reference equality here
        // we can't move towards doing Expr equality checks
        // until Expr.GetHashCode() is fixed to be a constant time
        // operation
        private HashSet<Constraint> InternalConstraints;

        public int Count
        {
            get { return InternalConstraints.Count; }
        }


        public IEnumerable<Expr> ConstraintExprs
        {
            get { return InternalConstraints.Select(c => c.Condition); }
        }

        public IEnumerable<Constraint> Constraints
        {
            get { return InternalConstraints; }
        }

        public ConstraintManager()
        {
            InternalConstraints = new HashSet<Constraint>();
        }

        public IConstraintManager DeepClone()
        {
            ConstraintManager other = (ConstraintManager) this.MemberwiseClone();
            other.InternalConstraints = new HashSet<Constraint>();

            // Constraints should be immutable so we don't need to clone the Expr
            foreach (var c in this.InternalConstraints)
            {
                other.InternalConstraints.Add(c);
            }

            return other;
        }

        public void AddConstraint(Expr e, ProgramLocation location)
        {
            Debug.Assert(e.ShallowType.IsBool, "Constraints stored must be boolean");

            // Drop Literal constraints (i.e. "True")
            if (e is LiteralExpr)
            {
                Debug.Assert(( e as LiteralExpr ).asBool, "Constraint cannot be false");
                return;
            }

            InternalConstraints.Add(new Constraint(e, location));
        }

        public IConstraintManager GetSubSet(ISet<Constraint> subset)
        {
            // Don't make a new ConstraintManager if the constraints are the same.
            if (InternalConstraints.SetEquals(subset))
                return this;

            // Is this the most efficient way to do this?
            ConstraintManager other = (ConstraintManager) this.MemberwiseClone();
            Debug.Assert(subset.IsSubsetOf(InternalConstraints), "argument ``subset`` is not a valid subset");

            if (subset is HashSet<Constraint>)
            {
                // Reuse the container for efficiency
                // This doesn't feel very safe...
                other.InternalConstraints = (HashSet<Constraint>) subset;
            }
            else
            {
                other.InternalConstraints = new HashSet<Constraint>();
                foreach (var constraint in subset)
                {
                    other.InternalConstraints.Add(constraint);
                }
            }

            return other;
        }

        public void Dump(TextWriter TW, bool showConstraints)
        {
            TW.WriteLine("[Constraints]");
            TW.WriteLine(InternalConstraints.Count + " constraint(s)");

            if (showConstraints)
            {
                foreach (var e in InternalConstraints)
                {
                    TW.WriteLine("Origin:" + e.Origin);
                    TW.WriteLine("Expr:" + e.Condition);
                    TW.WriteLine("# of used variables:" + e.UsedVariables.Count);
                    TW.WriteLine("");
                }
            }
        }

        public void Dump(TextWriter TW)
        {
            Dump(TW, true);
        }

        public override string ToString()
        {
            return ToString(false);
        }

        public string ToString(bool showConstraints)
        {
            string result = null;
            using (var SW = new StringWriter())
            {
                Dump(SW, showConstraints);
                result = SW.ToString();
            }
            return result;
        }
    }

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

        private void ComputeUsedVariablesAndUninterpretedFunctions()
        {
            this.InternalUsedVariables = new HashSet<SymbolicVariable>();
            var fsv = new FindSymbolicsVisitor(this.InternalUsedVariables);
            fsv.Visit(this.Condition);

            this.InternalUsedUninterpretedFunctions = new HashSet<Function>();
            var ffv = new FindFunctionsVisitor(this.InternalUsedUninterpretedFunctions);
            ffv.Visit(this.Condition);
        }
    }
}

