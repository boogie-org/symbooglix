using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.Numerics;

namespace Symbooglix
{
    public interface IExprBuilder
    {
        // Constants
        LiteralExpr ConstantInt(int value);
        LiteralExpr ConstantReal(string value);
        LiteralExpr ConstantBool(bool value);
        LiteralExpr ConstantBV(int decimalValue, int bitWidth);
        LiteralExpr ConstantBV(BigNum decimalValue, int bitWidth);
        LiteralExpr True { get;}
        LiteralExpr False { get; }

        // TODO
        // BitVector operators
        Expr BVSLT(Expr lhs, Expr rhs);
        Expr BVSLE(Expr lhs, Expr rhs);
        Expr BVSGT(Expr lhs, Expr rhs);
        Expr BVSGE(Expr lhls, Expr rhs);

        Expr BVAND(Expr lhs, Expr rhs);
        Expr BVOR(Expr lhs, Expr rhs);
        Expr BVXOR(Expr lhs, Expr rhs);
        Expr BVSHL(Expr lhs, Expr rhs);
        Expr BVLSHR(Expr lhs, Expr rhs);
        Expr BVASHR(Expr lhs, Expr rhs);

        Expr BVMUL(Expr lhs, Expr rhs);
        Expr BVUDIV(Expr lhs, Expr rhs);
        Expr BVUREM(Expr lhs, Expr rhs);
        Expr BVSDIV(Expr lhs, Expr rhs);
        Expr BVSREM(Expr lhs, Expr rhs);
        Expr BVSMOD(Expr lhs, Expr rhs);

        Expr BVNEG(Expr operand);
        Expr BVNOT(Expr operand);


        // Real/Int operators


        // Logical operators
        Expr And(Expr lhs, Expr rhs);
        Expr Or(Expr lhs, Expr rhs);
        Expr Eq(Expr lhs, Expr rhs);
        Expr NotEq(Expr lhs, Expr rhs);
        Expr Iff(Expr lhs, Expr rhs);
        Expr IfThenElse(Expr condition, Expr thenExpr, Expr elseExpr);
        Expr Not(Expr e);
    }


}

