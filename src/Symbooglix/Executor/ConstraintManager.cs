using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using Microsoft.Boogie;
using System.IO;

namespace Symbooglix
{

    public class ConstraintManager : Util.IDeepClone<ConstraintManager>
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

        public ConstraintManager DeepClone()
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

        public void Dump(TextWriter TW,  bool showConstraints, int indent)
        {
            string indentStr = new string(' ', indent);
            TW.WriteLine("[Constraints]");
            TW.WriteLine(indentStr + InternalConstraints.Count + " constraint(s)");

            if (showConstraints)
            {
                foreach (var e in InternalConstraints)
                {
                    TW.WriteLine(indentStr + "Origin:" + e.Origin);
                    TW.WriteLine(indentStr + "Expr:" + e.Condition);
                    TW.WriteLine(indentStr + "# of used variables:" + e.UsedVariables.Count);
                    TW.WriteLine("");
                }
            }
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
                Dump(SW, showConstraints ,4);
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

