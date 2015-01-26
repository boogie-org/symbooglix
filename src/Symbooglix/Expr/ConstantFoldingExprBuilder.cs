using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public class ConstantFoldingExprBuilder : DecoratorExprBuilder
    {
        public ConstantFoldingExprBuilder(IExprBuilder underlyingBuilder) : base(underlyingBuilder)
        {
        }

        // TODO Overload methods that we can constant fold

        public override Expr Add(Expr lhs, Expr rhs)
        {
            if (lhs is LiteralExpr && rhs is LiteralExpr)
            {
                var literalLhs = lhs as LiteralExpr;
                var literalRhs = rhs as LiteralExpr;
                if (literalLhs.isBigNum && literalRhs.isBigNum)
                {
                    // Int
                    var result = literalLhs.asBigNum + literalRhs.asBigNum;
                    return UB.ConstantInt(result.ToBigInteger);
                }
                else if (literalLhs.isBigDec && literalRhs.isBigDec)
                {
                    // Real
                    return UB.ConstantReal(literalLhs.asBigDec + literalRhs.asBigDec);
                }
            }

            return UB.Add(lhs, rhs);
        }
    }
}

