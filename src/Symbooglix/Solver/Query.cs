using System;
using Microsoft.Boogie;

namespace Symbooglix
{
    namespace Solver
    {
        public class Query
        {
            public IConstraintManager Constraints { get; private set;}
            public Constraint QueryExpr { get; private set;}
            public Query(IConstraintManager constraints, Constraint queryExpr)
            {
                this.Constraints = constraints;
                this.QueryExpr = queryExpr;
            }

            public Query WithNegatedQueryExpr()
            {
                var that = (Query) this.MemberwiseClone();
                that.QueryExpr = this.QueryExpr.GetNegatedConstraint();
                return that;
            }
        }
    }
}

