using System;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace Symbooglix
{

    public class ConstraintManager : Util.IDeepClone<ConstraintManager>
    {
        public List<Expr> constraints;
        public ConstraintManager()
        {
            constraints = new List<Expr>();
        }

        public ConstraintManager DeepClone()
        {
            ConstraintManager other = (ConstraintManager) this.MemberwiseClone();
            other.constraints = new List<Expr>();

            var duplicator = new NonSymbolicDuplicator();
            foreach (var e in this.constraints)
            {
                var copy = (Expr) duplicator.Visit(e);
                other.constraints.Add(copy);
            }

            return other;
        }

        public void addConstraint(Expr e)
        {
            constraints.Add(e);
        }

        public override string ToString()
        {
            string d = "[Constraints]\n";
            d += constraints.Count + " constraint(s)\n\n";

            foreach (Expr e in constraints)
                d += e + "\n";

            return d;
        }
    }
}

