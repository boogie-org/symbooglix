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
using Microsoft.Boogie;
using System.Numerics;
using System.Collections.Generic;

namespace Symbooglix
{
    public interface IExprBuilder
    {
        bool Immutable
        {
            get;
        }

        // Constants
        LiteralExpr ConstantInt(int value);
        LiteralExpr ConstantInt(BigInteger decimalValue);
        LiteralExpr ConstantReal(string value);
        LiteralExpr ConstantReal(Microsoft.Basetypes.BigDec value);
        LiteralExpr ConstantBool(bool value);
        LiteralExpr ConstantBV(int decimalValue, int bitWidth);
        LiteralExpr ConstantBV(BigInteger decimalValue, int bitWidth);
        LiteralExpr True { get;}
        LiteralExpr False { get; }
        Expr Identifier(Variable v);

        // BitVector operators
        Expr BVSLT(Expr lhs, Expr rhs);
        Expr BVSLE(Expr lhs, Expr rhs);
        Expr BVSGT(Expr lhs, Expr rhs);
        Expr BVSGE(Expr lhls, Expr rhs);

        Expr BVULT(Expr lhs, Expr rhs);
        Expr BVULE(Expr lhs, Expr rhs);
        Expr BVUGT(Expr lhs, Expr rhs);
        Expr BVUGE(Expr lhs, Expr rhs);

        Expr BVAND(Expr lhs, Expr rhs);
        Expr BVOR(Expr lhs, Expr rhs);
        Expr BVXOR(Expr lhs, Expr rhs);
        Expr BVSHL(Expr lhs, Expr rhs);
        Expr BVLSHR(Expr lhs, Expr rhs);
        Expr BVASHR(Expr lhs, Expr rhs);

        Expr BVADD(Expr lhs, Expr rhs);
        Expr BVSUB(Expr lhs, Expr rhs);
        Expr BVMUL(Expr lhs, Expr rhs);
        Expr BVUDIV(Expr lhs, Expr rhs);
        Expr BVUREM(Expr lhs, Expr rhs);
        Expr BVSDIV(Expr lhs, Expr rhs);
        Expr BVSREM(Expr lhs, Expr rhs);
        Expr BVSMOD(Expr lhs, Expr rhs);

        Expr BVNEG(Expr operand);
        Expr BVNOT(Expr operand);

        Expr BVSEXT(Expr operand, int newWidth);
        Expr BVZEXT(Expr operand, int newWidth);
        Expr BVCONCAT(Expr MSB, Expr LSB);
        // Interval is (end, start]
        Expr BVEXTRACT(Expr operand, int end, int start);


        // Real/Int operators
        Expr Add(Expr lhs, Expr rhs);
        Expr Sub(Expr lhs, Expr rhs);
        Expr Mul(Expr lhs, Expr rhs);
        Expr Mod(Expr lhs, Expr rhs);
        Expr Rem(Expr lhs, Expr rhs);

        // Flooring division (operands must be of type int). Returns an int
        Expr Div(Expr lhs, Expr rhs);
        // Real Division (operands can be either int or real. The types can be mixed)
        Expr RealDiv(Expr lhs, Expr rhs);
        // Exponentiation (operands must be of type real). Returns a real
        Expr Pow(Expr lhs, Expr rhs);
        Expr Neg(Expr operand);
        Expr ArithmeticCoercion(ArithmeticCoercion.CoercionType coercionType, Expr operand);


        // Logical operators
        Expr And(Expr lhs, Expr rhs);
        Expr Or(Expr lhs, Expr rhs);
        Expr Iff(Expr lhs, Expr rhs);
        Expr Imp(Expr lhs, Expr rhs);
        Expr IfThenElse(Expr condition, Expr thenExpr, Expr elseExpr);
        Expr Not(Expr e);

        // Comparison Operators (real and int) only
        Expr Eq(Expr lhs, Expr rhs);
        Expr NotEq(Expr lhs, Expr rhs);
        Expr Lt(Expr lhs, Expr rhs);
        Expr Le(Expr lhs, Expr rhs);
        Expr Gt(Expr lhs, Expr rhs);
        Expr Ge(Expr lhs, Expr rhs);

        // Uninterpreted functions
        Expr UFC(FunctionCall func, params Expr[] args);

        // Maps
        Expr MapSelect(Expr map, params Expr[] indices);
        Expr MapStore(Expr map, Expr value, params Expr[] indices);

        Expr Old(Expr operand);

        // Quantifiers
        // triggers should be set to null if there are no triggers.
        // FIXME: Boogie's API for triggers is gross (eurgh.. linked list)
        Expr ForAll(IList<Variable> freeVars, Expr body, Trigger triggers);
        Expr Exists(IList<Variable> freeVargs, Expr body, Trigger triggers);

        Expr Distinct(IList<Expr> exprs);
    }

    // FIXME: This class should probably contain references to the relevant Exprs
    public class ExprTypeCheckException : Exception
    {
        public ExprTypeCheckException(string msg) : base(msg) { }
    }


}

