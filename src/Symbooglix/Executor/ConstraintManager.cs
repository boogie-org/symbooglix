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
        // The implementation is deliberatly hidden from users
        // because we might later change to container. E.g. perhaps
        // we might move to a set rather than a list.
        private List<Constraint> InternalConstraints;

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
            InternalConstraints = new List<Constraint>();
        }

        public IConstraintManager DeepClone()
        {
            ConstraintManager other = (ConstraintManager) this.MemberwiseClone();
            other.InternalConstraints = new List<Constraint>();

            // Constraints should be immutable so we don't need to clone the Expr
            foreach (var c in this.InternalConstraints)
            {
                other.InternalConstraints.Add(c);
            }

            return other;
        }

        public void AddConstraint(Expr e, ProgramLocation location)
        {
            InternalConstraints.Add(new Constraint(e, location));
        }

        public IConstraintManager GetSubSet(ISet<Constraint> subset)
        {
            throw new NotImplementedException();
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

        public Constraint(Expr condition)
        {
            Condition = condition;
            Debug.Assert(condition.Type.IsBool, "Constraint must be a boolean expression!");
            Origin = null;
            ComputeUsedVariables();
        }

        public Constraint(Expr condition, ProgramLocation location) : this(condition)
        {
            Debug.Assert(location != null);
            Origin = location;
            ComputeUsedVariables();
        }

        private void ComputeUsedVariables()
        {
            this.InternalUsedVariables = new HashSet<SymbolicVariable>();
            var fsv = new FindSymbolicsVisitor(this.InternalUsedVariables);
            fsv.Visit(this.Condition);
        }
    }
}

