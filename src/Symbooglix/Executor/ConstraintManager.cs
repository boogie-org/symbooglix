using System;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace Symbooglix
{

    public class ConstraintManager : Util.IDeepClone<ConstraintManager>
    {
        public List<Expr> Constraints;
        public ConstraintManager()
        {
            Constraints = new List<Expr>();
        }

        public ConstraintManager DeepClone()
        {
            ConstraintManager other = (ConstraintManager) this.MemberwiseClone();
            other.Constraints = new List<Expr>();

            var duplicator = new NonSymbolicDuplicator();
            foreach (var e in this.Constraints)
            {
                var copy = (Expr) duplicator.Visit(e);
                other.Constraints.Add(copy);
            }

            return other;
        }

        public void AddConstraint(Expr e)
        {
            Constraints.Add(e);
        }

        public override string ToString()
        {
            string d = "[Constraints]\n";
            d += Constraints.Count + " constraint(s)\n\n";

            foreach (Expr e in Constraints)
                d += e + "\n";

            return d;
        }
    }
}

