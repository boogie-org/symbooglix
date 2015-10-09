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
using System.Linq;
using Microsoft.Boogie;
using System.IO;
using System.Collections.Immutable;

namespace Symbooglix
{
    public interface IConstraintManager : Util.IYAMLWriter
    {
        int Count { get; }
        IEnumerable<Expr> ConstraintExprs{ get; }
        IEnumerable<Constraint> Constraints { get; }
        void AddConstraint(Expr e, ProgramLocation location);
        void AddConstraint(Constraint c);
        bool Contains(Constraint c);

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
        private ImmutableHashSet<Constraint>.Builder InternalConstraints;

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

        // The hashcode is iteratively computed everytime a new constraint is added
        private int PreComputedHashCode = 0;
        public ConstraintManager()
        {
            var empty = ImmutableHashSet<Constraint>.Empty;
            InternalConstraints = empty.ToBuilder();
        }

        private void FullyRecomputeHashCode()
        {
            PreComputedHashCode = 0;
            foreach (var c in InternalConstraints)
            {
                UpdateHashCode(c);
            }
        }

        // Used to iteratively update the hash code every time a new constraint is added
        private void UpdateHashCode(Constraint c)
        {
            PreComputedHashCode = ( 97 * PreComputedHashCode ) + c.GetHashCode();
        }

        public IConstraintManager Clone()
        {
            ConstraintManager other = (ConstraintManager) this.MemberwiseClone();
            var asImmutable = this.InternalConstraints.ToImmutable();
            other.InternalConstraints = asImmutable.ToBuilder();

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
            UpdateHashCode(c);
        }

        public IConstraintManager GetSubSet(ISet<Constraint> subset)
        {
            // Don't make a new ConstraintManager if the constraints are the same.
            if (InternalConstraints.SetEquals(subset))
                return this;

            if (subset.Count >= InternalConstraints.Count)
                throw new ArgumentException("Subset has count >= to count of this constraint manager's constraints");

            // Is this the most efficient way to do this?
            ConstraintManager other = (ConstraintManager) this.MemberwiseClone();
            Debug.Assert(subset.IsSubsetOf(InternalConstraints), "argument ``subset`` is not a valid subset");

            var asIm = ImmutableHashSet<Constraint>.Empty.Union(subset);
            other.InternalConstraints = asIm.ToBuilder();

            // Fully recompute the hashcode on the new constraint manager
            other.FullyRecomputeHashCode();
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

        public override bool Equals(object obj)
        {
            if (obj == null)
                return false;

            var other = obj as ConstraintManager;
            if (other == null)
                return false;

            if (this.Count != other.Count)
                return false;

            return this.InternalConstraints.SetEquals(other.InternalConstraints);

        }

        public override int GetHashCode()
        {
            return this.PreComputedHashCode;
        }

        public bool Contains(Constraint c)
        {
            return InternalConstraints.Contains(c);
        }
    }

}

