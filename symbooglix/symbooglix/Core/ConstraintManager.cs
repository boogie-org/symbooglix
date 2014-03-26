using System;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace symbooglix
{

    public class ConstraintManager : util.IDeepClone<ConstraintManager>
    {
        public List<Expr> constraints;
        public ConstraintManager()
        {
            constraints = new List<Expr>();
        }

        public ConstraintManager DeepClone()
        {
            throw new NotImplementedException();
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

