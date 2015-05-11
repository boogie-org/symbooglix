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
        void AddConstraint(Constraint c);

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

        protected HashSet<Constraint> GetNewHashSet()
        {
            // Use a special IEqualityComparer<Constraint> that only looks
            // at Constraint.Expr because we only care about that
            return new HashSet<Constraint>(new ConstraintInHashSetCompare());
        }

        public ConstraintManager()
        {
            InternalConstraints = GetNewHashSet();
        }

        public IConstraintManager Clone()
        {
            ConstraintManager other = (ConstraintManager) this.MemberwiseClone();
            other.InternalConstraints = GetNewHashSet();

            // Constraints should be immutable so we don't need to clone the Expr
            foreach (var c in this.InternalConstraints)
            {
                other.InternalConstraints.Add(c);
            }

            return other;
        }


        public void AddConstraint(Expr e, ProgramLocation location)
        {
            AddConstraint(new Constraint(e, location));
        }

        public void AddConstraint(Constraint c)
        {
            if (ExprUtil.IsFalse(c.Condition))
                throw new Exception("Cannot add false to constraint set");

            Debug.Assert(c.Condition.ShallowType.IsBool, "constraint must be boolean");
            InternalConstraints.Add(c);
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
                // FIXME: Remove this hack and see if it makes much of a performance difference
                // Reuse the container for efficiency
                // This doesn't feel very safe...
                other.InternalConstraints = (HashSet<Constraint>) subset;
            }
            else
            {
                other.InternalConstraints = GetNewHashSet();
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

}

