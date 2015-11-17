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
using Microsoft.Basetypes;
using Microsoft.Boogie;
using System.Numerics;
using System.Collections.Generic;

namespace Symbooglix
{
    // This provides a convenient super class for classes to use becuase
    // they can selectively implement the methods they are interested in to make
    // implementing an IExprBuilder much simpler
    public class DecoratorExprBuilder : IExprBuilder
    {
        public IExprBuilder UB;
        public bool Immutable
        {
            get { return UB.Immutable; }
        }

        public DecoratorExprBuilder(IExprBuilder underlyingBuilder)
        {
            UB = underlyingBuilder;
        }

        public virtual LiteralExpr True 
        {
            get 
            {
                return UB.True;
            }
        }

        public virtual LiteralExpr False
        {
            get
            {
                return UB.False;
            }
        }

        public Expr Identifier(Variable v)
        {
            return UB.Identifier(v);
        }

        public virtual LiteralExpr ConstantInt(int value)
        {
            return UB.ConstantInt(value);
        }

        public virtual LiteralExpr ConstantInt(BigInteger decimalValue)
        {
            return UB.ConstantInt(decimalValue);
        }

        public virtual LiteralExpr ConstantReal(string value)
        {
            return UB.ConstantReal(value);
        }

        public virtual LiteralExpr ConstantReal(BigDec value)
        {
            return UB.ConstantReal(value);
        }

        public virtual LiteralExpr ConstantBool(bool value)
        {
            return UB.ConstantBool(value);
        }

        public virtual LiteralExpr ConstantBV(int decimalValue, int bitWidth)
        {
            return UB.ConstantBV(decimalValue, bitWidth);
        }

        public virtual LiteralExpr ConstantBV (BigInteger decimalValue, int bitWidth)
        {
            return UB.ConstantBV(decimalValue, bitWidth);
        }

        public virtual Expr BVSLT(Expr lhs, Expr rhs)
        {
            return UB.BVSLT(lhs, rhs);
        }

        public virtual Expr BVSLE(Expr lhs, Expr rhs)
        {
            return UB.BVSLE(lhs, rhs);
        }

        public virtual Expr BVSGT(Expr lhs, Expr rhs)
        {
            return UB.BVSGT(lhs, rhs);
        }

        public virtual Expr BVSGE(Expr lhs, Expr rhs)
        {
            return UB.BVSGE(lhs, rhs);
        }

        public virtual Expr BVULT(Expr lhs, Expr rhs)
        {
            return UB.BVULT(lhs, rhs);
        }

        public virtual Expr BVULE(Expr lhs, Expr rhs)
        {
            return UB.BVULE(lhs, rhs);
        }

        public virtual Expr BVUGT(Expr lhs, Expr rhs)
        {
            return UB.BVUGT(lhs, rhs);
        }

        public virtual Expr BVUGE(Expr lhs, Expr rhs)
        {
            return UB.BVUGE(lhs, rhs);
        }

        public virtual Expr BVAND(Expr lhs, Expr rhs)
        {
            return UB.BVAND(lhs, rhs);
        }

        public virtual Expr BVOR(Expr lhs, Expr rhs)
        {
            return UB.BVOR(lhs, rhs);
        }

        public virtual Expr BVXOR(Expr lhs, Expr rhs)
        {
            return UB.BVXOR(lhs, rhs);
        }

        public virtual Expr BVSHL(Expr lhs, Expr rhs)
        {
            return UB.BVSHL(lhs, rhs);
        }

        public virtual Expr BVLSHR(Expr lhs, Expr rhs)
        {
            return UB.BVLSHR(lhs, rhs);
        }

        public virtual Expr BVASHR(Expr lhs, Expr rhs)
        {
            return UB.BVASHR(lhs, rhs);
        }

        public virtual Expr BVADD(Expr lhs, Expr rhs)
        {
            return UB.BVADD(lhs, rhs);
        }

        public virtual Expr BVSUB(Expr lhs, Expr rhs)
        {
            return UB.BVSUB(lhs, rhs);
        }

        public virtual Expr BVMUL(Expr lhs, Expr rhs)
        {
            return UB.BVMUL(lhs, rhs);
        }

        public virtual Expr BVUDIV(Expr lhs, Expr rhs)
        {
            return UB.BVUDIV(lhs, rhs);
        }

        public virtual Expr BVUREM(Expr lhs, Expr rhs)
        {
            return UB.BVUREM(lhs, rhs);
        }

        public virtual Expr BVSDIV(Expr lhs, Expr rhs)
        {
            return UB.BVSDIV(lhs, rhs);
        }

        public virtual Expr BVSREM(Expr lhs, Expr rhs)
        {
            return UB.BVSREM(lhs, rhs);
        }

        public virtual Expr BVSMOD(Expr lhs, Expr rhs)
        {
            return UB.BVSMOD(lhs, rhs);
        }

        public virtual Expr BVNEG(Expr operand)
        {
            return UB.BVNEG(operand);
        }

        public virtual Expr BVNOT(Expr operand)
        {
            return UB.BVNOT(operand);
        }

        public virtual Expr BVSEXT(Expr operand, int newWidth)
        {
            return UB.BVSEXT(operand, newWidth);
        }

        public virtual Expr BVZEXT(Expr operand, int newWidth)
        {
            return UB.BVZEXT(operand, newWidth);
        }

        public virtual Expr BVCONCAT(Expr MSB, Expr LSB)
        {
            return UB.BVCONCAT(MSB, LSB);
        }

        public virtual Expr BVEXTRACT(Expr operand, int end, int start)
        {
            return UB.BVEXTRACT(operand, end, start);
        }

        public virtual Expr Add(Expr lhs, Expr rhs)
        {
            return UB.Add(lhs, rhs);
        }

        public virtual Expr Sub(Expr lhs, Expr rhs)
        {
            return UB.Sub(lhs, rhs);
        }

        public virtual Expr Mul(Expr lhs, Expr rhs)
        {
            return UB.Mul(lhs, rhs);
        }

        public virtual Expr Mod(Expr lhs, Expr rhs)
        {
            return UB.Mod(lhs, rhs);
        }

        public virtual Expr Rem(Expr lhs, Expr rhs)
        {
            return UB.Rem(lhs, rhs);
        }

        public virtual Expr Div(Expr lhs, Expr rhs)
        {
            return UB.Div(lhs, rhs);
        }

        public virtual Expr RealDiv(Expr lhs, Expr rhs)
        {
            return UB.RealDiv(lhs, rhs);
        }

        public virtual Expr Pow(Expr lhs, Expr rhs)
        {
            return UB.Pow(lhs, rhs);
        }

        public virtual Expr And(Expr lhs, Expr rhs)
        {
            return UB.And(lhs, rhs);
        }

        public virtual Expr Or(Expr lhs, Expr rhs)
        {
            return UB.Or(lhs, rhs);
        }

        public virtual Expr Eq(Expr lhs, Expr rhs)
        {
            return UB.Eq(lhs, rhs);
        }

        public virtual Expr NotEq(Expr lhs, Expr rhs)
        {
            return UB.NotEq(lhs, rhs);
        }

        public virtual Expr Iff(Expr lhs, Expr rhs)
        {
            return UB.Iff(lhs, rhs);
        }

        public virtual Expr Imp(Expr lhs, Expr rhs)
        {
            return UB.Imp(lhs, rhs);
        }

        public virtual Expr IfThenElse(Expr condition, Expr thenExpr, Expr elseExpr)
        {
            return UB.IfThenElse(condition, thenExpr, elseExpr);
        }

        public virtual Expr Not(Expr e)
        {
            return UB.Not(e);
        }

        public virtual Expr Neg(Expr e)
        {
            return UB.Neg(e);
        }

        public virtual Expr UFC(FunctionCall func, params Expr[] args)
        {
            return UB.UFC(func, args);
        }

        public virtual Expr MapSelect(Expr map, params Expr[] indices)
        {
            return UB.MapSelect(map, indices);
        }

        public virtual Expr MapStore(Expr map, Expr value, params Expr[] indices)
        {
            return UB.MapStore(map, value, indices);
        }

        public virtual Expr ArithmeticCoercion(ArithmeticCoercion.CoercionType coercionType, Expr operand)
        {
            return UB.ArithmeticCoercion(coercionType, operand);
        }

        public virtual Expr Lt(Expr lhs, Expr rhs)
        {
            return UB.Lt(lhs, rhs);
        }

        public virtual Expr Le(Expr lhs, Expr rhs)
        {
            return UB.Le(lhs, rhs);
        }

        public virtual Expr Gt(Expr lhs, Expr rhs)
        {
            return UB.Gt(lhs, rhs);
        }

        public virtual Expr Ge(Expr lhs, Expr rhs)
        {
            return UB.Ge(lhs, rhs);
        }

        public virtual Expr Old(Expr operand)
        {
            return UB.Old(operand);
        }

        public virtual Expr ForAll(IList<Variable> freeVars, Expr body, Trigger triggers)
        {
            return UB.ForAll(freeVars, body, triggers);
        }

        public virtual Expr Exists(IList<Variable> freeVargs, Expr body, Trigger triggers)
        {
            return UB.Exists(freeVargs, body, triggers);
        }

        public Expr Distinct(IList<Expr> exprs)
        {
            return UB.Distinct(exprs);
        }
    }
}

