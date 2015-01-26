using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Microsoft.Boogie;
using System.IO;

namespace Symbooglix
{
    public interface IConstraintManager : Util.IYAMLWriter
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

        void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW, bool showConstraints);
        IConstraintManager Clone();
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

        public IConstraintManager Clone()
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

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            WriteAsYAML(TW, /*showConstaints=*/ false);
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW, bool showConstraints)
        {
            TW.WriteLine("num_constraints: {0}", Count);
            if (!showConstraints)
                return;

            TW.WriteLine("constraints:");
            TW.Indent += 1;
            if (InternalConstraints.Count == 0)
            {
                TW.WriteLine("[ ]");
            }
            else
            {
                foreach (var e in InternalConstraints)
                {
                    TW.WriteLine("-");
                    TW.Indent += 1;
                    TW.WriteLine("origin: \"{0}\"", e.Origin);
                    TW.WriteLine("expr: \"{0}\"", e.Condition);
                    TW.WriteLine("num_used_variables: {0}", e.UsedVariables.Count);
                    TW.WriteLine("num_used_uf: {0}", e.UsedUninterpretedFunctions.Count);
                    TW.Indent -= 1;
                }
            }
            TW.Indent -= 1;
        }

        public override string ToString()
        {
            string result = null;
            using (var SW = new StringWriter())
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
            var ffv = new FindUinterpretedFunctionsVisitor(this.InternalUsedUninterpretedFunctions);
            ffv.Visit(this.Condition);
        }
    }
}

