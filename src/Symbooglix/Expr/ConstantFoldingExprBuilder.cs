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
using Microsoft.Basetypes;
using System.Collections.Generic;
using System.Diagnostics;
using System.Numerics;

namespace Symbooglix
{
    public class ConstantFoldingExprBuilder : DecoratorExprBuilder
    {
        public ConstantFoldingExprBuilder(IExprBuilder underlyingBuilder) : base(underlyingBuilder)
        {
        }

        // TODO Overload methods that we can constant fold

        // We have to be very careful here. These methods are called before typechecking so we should
        // make sure things are the right type before doing anything crazy

        public override Expr Add(Expr lhs, Expr rhs)
        {
            // TODO: Implement x +x => 2*x for arbitary x

            // Ensure if we have at least one constant its always on the lhs
            // we can do this because + is commutative
            if (rhs is LiteralExpr)
            {
                // a + b ==> b + a
                Expr temp = lhs;
                lhs = rhs;
                rhs = temp;
            }

            var literalLhs = lhs as LiteralExpr;
            var literalRhs = rhs as LiteralExpr;

            if (literalLhs != null && literalRhs != null)
            {
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

            // 0 + x => x
            if (literalLhs != null)
            {
                if (literalLhs.isBigDec && literalLhs.asBigDec.IsZero)
                {
                    return rhs;
                }
                else if (literalLhs.isBigNum && literalLhs.asBigNum.IsZero)
                {
                    return rhs;
                }
            }

            // Associativy a + (b + c) ==> (a + b) + c
            // if a and b are constants (that's why we enforce constants on left)
            // then we can fold into a single "+" operation
            // FIXME: Need an easier way of checking operator type
            var rhsAsAdd = ExprUtil.AsAdd(rhs);
            if (rhsAsAdd != null)
            {
                var rhsAddLeftLiteral = ExprUtil.AsLiteral(rhsAsAdd.Args[0]);
                if (rhsAddLeftLiteral != null)
                {
                    if (literalLhs != null)
                    {
                        //     +
                        //    / \
                        //   1   +
                        //      / \
                        //      2 x
                        // fold to
                        // 3 + x
                        if (literalLhs.isBigNum && rhsAddLeftLiteral.isBigNum)
                        {
                            // Int
                            var result = this.ConstantInt(( literalLhs.asBigNum + rhsAddLeftLiteral.asBigNum ).ToBigInteger);
                            return this.Add(result, rhsAsAdd.Args[1]);
                        }
                        else if (literalLhs.isBigDec && rhsAddLeftLiteral.isBigDec)
                        {
                            //real
                            var result = this.ConstantReal(literalLhs.asBigDec + rhsAddLeftLiteral.asBigDec);
                            return this.Add(result, rhsAsAdd.Args[1]);
                        }
                    }
                    else
                    {
                        //     +
                        //    / \
                        //   x   +
                        //      / \
                        //     1  y
                        // propagate constant up
                        //  1 + (x + y)
                        var newSubExprAdd = this.Add(lhs, rhsAsAdd.Args[1]);
                        return this.Add(rhsAddLeftLiteral, newSubExprAdd);
                    }
                }
            }

            // <expr> + <expr> => 2*<expr>
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                if (lhs.Type.IsInt)
                {
                    return this.Mul(this.ConstantInt(2), lhs);
                }
                else if (rhs.Type.IsReal)
                {
                    return this.Mul(this.ConstantReal("2.0"), lhs);
                }
                else
                    throw new ExprTypeCheckException("operands to Add must be of int or real type");
            }

            // Can't constant fold
            return UB.Add(lhs, rhs);
        }

        public override Expr Mul(Expr lhs, Expr rhs)
        {

            // Ensure if we have at least one constant its always on the lhs
            // we can do this because + is commutative
            if (rhs is LiteralExpr)
            {
                // a + b ==> b + a
                Expr temp = lhs;
                lhs = rhs;
                rhs = temp;
            }

            var literalLhs = lhs as LiteralExpr;
            var literalRhs = rhs as LiteralExpr;

            if (literalLhs != null && literalRhs != null)
            {
                if (literalLhs.isBigNum && literalRhs.isBigNum)
                {
                    // Int
                    var result = literalLhs.asBigNum * literalRhs.asBigNum;
                    return UB.ConstantInt(result.ToBigInteger);
                }
                else if (literalLhs.isBigDec && literalRhs.isBigDec)
                {
                    // Real
                    return UB.ConstantReal(literalLhs.asBigDec * literalRhs.asBigDec);
                }
            }

            // 0 * x ==> 0
            if (literalLhs != null)
            {
                if (literalLhs.isBigDec && literalLhs.asBigDec.IsZero)
                {
                    return this.ConstantReal("0.0");
                }
                else if (literalLhs.isBigNum && literalLhs.asBigNum.IsZero)
                {
                    return this.ConstantInt(BigNum.ZERO.ToBigInteger);
                }
            }

            // 1 * <expr> ==> <expr>
            if (literalLhs != null)
            {
                if (literalLhs.isBigDec && literalLhs.asBigDec.Mantissa.IsOne)
                {
                    return rhs;
                }
                else if (literalLhs.isBigNum && literalLhs.asBigNum.ToBigInteger.IsOne)
                {
                    return rhs;
                }
            }

            // Associativy a * (b * c) ==> (a * b) * c
            // if a and b are constants (that's why we enforce constants on left)
            // then we can fold into a single "*" operation
            var rhsAsMul = ExprUtil.AsMul(rhs);
            if (rhsAsMul != null)
            {
                var rhsMulLeftLiteral = ExprUtil.AsLiteral(rhsAsMul.Args[0]);
                if (rhsMulLeftLiteral != null)
                {
                    if (literalLhs != null)
                    {
                        //     *
                        //    / \
                        //   1   *
                        //      / \
                        //     2  x
                        // fold to
                        // 2 * x
                        var result = this.Mul(literalLhs, rhsMulLeftLiteral);
                        return this.Mul(result, rhsAsMul.Args[1]);
                    }
                    else
                    {
                        //     *
                        //    / \
                        //   x   *
                        //      / \
                        //     1  y
                        // propagate constant up
                        //  1 * (x * y)
                        var newSubExprMul = this.Mul(lhs, rhsAsMul.Args[1]);
                        return this.Mul(rhsMulLeftLiteral, newSubExprMul);
                    }
                }
            }

            // Can't constant fold
            return UB.Mul(lhs, rhs);
        }

        public override Expr IfThenElse(Expr condition, Expr thenExpr, Expr elseExpr)
        {
            var litCondition = condition as LiteralExpr;
            var litThenExpr = thenExpr as LiteralExpr;
            var litElseExpr = elseExpr as LiteralExpr;

            if (litCondition != null)
            {
                if (litCondition.IsTrue)
                {
                    // (if true then <exprA> else <exprB> ) ==> <exprA>
                    return thenExpr;
                }
                else if (litCondition.IsFalse)
                {
                    // (if false then <exprA> else <exprB> ) ==> <exprB>
                    return elseExpr;
                }

            }

            if (litThenExpr != null && litElseExpr != null)
            {
                // if <expr> then true else false ==> <expr>
                if (litThenExpr.IsTrue && litElseExpr.IsFalse)
                {
                    if (!condition.Type.IsBool)
                        throw new ExprTypeCheckException("condition to IfThenElse must be boolean");

                    return condition;
                }

                // if <expr> then false else true ==> !<expr>
                if (litThenExpr.IsFalse && litElseExpr.IsTrue)
                {
                    if (!condition.Type.IsBool)
                        throw new ExprTypeCheckException("condition to IfThenElse must be boolean");

                    return this.Not(condition);
                }
            }


            // if <expr> then <expr> else false ==> <expr>
            // e.g.
            // p1$1:bool := (if BV32_SLT(symbolic_5, 100bv32) then BV32_SLT(symbolic_5, 100bv32) else false)
            if (litElseExpr != null)
            {
                if (litElseExpr.IsFalse)
                {
                    if (ExprUtil.StructurallyEqual(condition, thenExpr))
                    {
                        return thenExpr;
                    }
                }
            }

            // if !<expr> then <expr> else true ==> <expr>
            // e.g.
            // p0$1:bool := (if !BV32_SLT(symbolic_5, 100bv32) then BV32_SLT(symbolic_5, 100bv32) else true)
            if (litElseExpr != null)
            {
                if (litElseExpr.IsTrue)
                {
                    var notExpr = ExprUtil.AsNot(condition);
                    if (notExpr != null)
                    {
                        if (ExprUtil.StructurallyEqual(notExpr.Args[0], thenExpr))
                            return thenExpr;
                    }
                }
            }


            //  if <expr> then true else <expr> ==> <expr>
            // e.g. (if BV32_SLT(symbolic_4, symbolic_20) then true else BV32_SLT(symbolic_4, symbolic_20))
            if (litThenExpr != null)
            {
                if (litThenExpr.IsTrue)
                {
                    if (condition.Equals(elseExpr))
                    {
                        return condition;
                    }
                }
            }

            // if <expr> then <expr2> else <expr2> ==> <expr2>
            if (ExprUtil.StructurallyEqual(thenExpr, elseExpr))
            {
                return thenExpr;
            }

            // we can't constant fold
            return UB.IfThenElse(condition, thenExpr, elseExpr);
        }

        public override Expr NotEq(Expr lhs, Expr rhs)
        {
            if (ExprUtil.AsLiteral(rhs) != null)
            {
                // Swap so we always have a constant on the left if at least one operand is a constant
                Expr temp = lhs;
                lhs = rhs;
                rhs = temp;
            }

            var litLhs = ExprUtil.AsLiteral(lhs);
            var litRhs = ExprUtil.AsLiteral(rhs);
            if (litLhs != null && litRhs != null)
            {
                if (litLhs.isBvConst && litRhs.isBvConst)
                {
                    if (litLhs.asBvConst.Equals(litRhs.asBvConst)) // make sure we use Equals and not ``==`` which does reference equality
                        return this.False;
                    else
                        return this.True;
                }
                else if (litLhs.isBool && litRhs.isBool)
                {
                    if (litLhs.asBool == litRhs.asBool)
                        return this.False;
                    else
                        return this.True;

                }
                else if (litLhs.isBigNum && litRhs.isBigNum)
                {
                    if (litLhs.asBigNum.Equals(litRhs.asBigNum))
                        return this.False;
                    else
                        return this.True;

                }
                else if (litLhs.isBigDec && litRhs.isBigDec)
                {
                    if (litLhs.asBigDec.Equals(litRhs.asBigDec))
                        return this.False;
                    else
                        return this.True;
                }
                else
                    throw new NotImplementedException(); // Unreachable?
            }

            // Inspired by the following GPUVerify specific example
            // e.g. (in axioms)
            // (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;
            // fold to group_size_y == 1bv32
            //
            // Unlike most of the optimisations this is a top down optimsation
            // rather than bottom up
            if (litLhs != null && ExprUtil.AsIfThenElse(rhs) != null)
            {
                var ift = rhs as NAryExpr;

                Debug.Assert(ift.Args.Count == 3);
                var thenExpr = ift.Args[1];
                var elseExpr = ift.Args[2];

                // Try to partially evaluate
                var thenExprEval = this.NotEq(litLhs, thenExpr);
                var elseExprEval = this.NotEq(litLhs, elseExpr);

                if (ExprUtil.AsLiteral(thenExprEval) != null || ExprUtil.AsLiteral(elseExprEval) != null)
                {
                    // Build a new if-then-else, which is simplified
                    return this.IfThenElse(ift.Args[0], thenExprEval, elseExprEval);
                }
            }

            // <expr> != <expr> ==> false
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                return this.False;
            }

            // Can't fold
            return UB.NotEq(lhs, rhs);
        }

        public override Expr Eq(Expr lhs, Expr rhs)
        {
            if (ExprUtil.AsLiteral(rhs) != null)
            {
                // Swap so we always have a constant on the left if at least one operand is a constant
                Expr temp = lhs;
                lhs = rhs;
                rhs = temp;
            }

            var litLhs = ExprUtil.AsLiteral(lhs);
            var litRhs = ExprUtil.AsLiteral(rhs);
            if (litLhs != null && litRhs != null)
            {
                if (litLhs.isBvConst && litRhs.isBvConst)
                {
                    if (litLhs.asBvConst.Equals(litRhs.asBvConst)) // make sure we use Equals and not ``==`` which does reference equality
                        return this.True;
                    else
                        return this.False;
                }
                else if (litLhs.isBool && litRhs.isBool)
                {
                    if (litLhs.asBool == litRhs.asBool)
                        return this.True;
                    else
                        return this.False;

                }
                else if (litLhs.isBigNum && litRhs.isBigNum)
                {
                    if (litLhs.asBigNum.Equals(litRhs.asBigNum))
                        return this.True;
                    else
                        return this.False;

                }
                else if (litLhs.isBigDec && litRhs.isBigDec)
                {
                    if (litLhs.asBigDec.Equals(litRhs.asBigDec))
                        return this.True;
                    else
                        return this.False;
                }
                else
                    throw new NotImplementedException(); // Unreachable?
            }

            // Inspired by the following GPUVerify specific example
            // e.g. (in axioms)
            // (if group_size_y == 1bv32 then 0bv1 else 1bv1) == 0bv1;
            // fold to group_size_y == 1bv32
            //
            // Unlike most of the optimisations this is a top down optimsation
            // rather than bottom up
            if (litLhs != null && ExprUtil.AsIfThenElse(rhs) != null)
            {
                var ift = rhs as NAryExpr;

                Debug.Assert(ift.Args.Count == 3);
                var thenExpr = ift.Args[1];
                var elseExpr = ift.Args[2];

                // Try to partially evaluate
                var thenExprEval = this.Eq(litLhs, thenExpr);
                var elseExprEval = this.Eq(litLhs, elseExpr);

                if (ExprUtil.AsLiteral(thenExprEval) != null || ExprUtil.AsLiteral(elseExprEval) != null)
                {
                    // Build a new if-then-else, which is simplified
                    return this.IfThenElse(ift.Args[0], thenExprEval, elseExprEval);
                }
            }

            // <expr> == <expr> ==> true
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                return this.True;
            }

            // Can't fold
            return UB.Eq(lhs, rhs);
        }

        public override Expr Not(Expr e)
        {
            var literal = ExprUtil.AsLiteral(e);

            if (literal != null)
            {
                if (literal.IsTrue)
                    return this.False;
                else if (literal.IsFalse)
                    return this.True;
                else
                    throw new Exception("Invalid operand to Not");
            }

            // ! (e0 == e1) ==> e0 != e1
            var asEq = ExprUtil.AsEq(e);
            if (asEq != null)
            {
                return this.NotEq(asEq.Args[0], asEq.Args[1]);
            }

            // !!<expr> ==> <expr>
            var asNot = ExprUtil.AsNot(e);
            if (asNot != null)
            {
                return asNot.Args[0];
            }

            // !(x > y) ==> ( x <= y )
            var asGt = ExprUtil.AsGt(e);
            if (asGt != null)
            {
                return this.Le(asGt.Args[0], asGt.Args[1]);
            }

            // !(x >= y) ==> ( x < y )
            var asGe = ExprUtil.AsGe(e);
            if (asGe != null)
            {
                return this.Lt(asGe.Args[0], asGe.Args[1]);
            }

            // !(x < y) ==> ( x >= y )
            var asLt = ExprUtil.AsLt(e);
            if (asLt != null)
            {
                return this.Ge(asLt.Args[0], asLt.Args[1]);
            }

            // !(x <= y) ==> ( x > y )
            var asLe = ExprUtil.AsLe(e);
            if (asLe != null)
            {
                return this.Gt(asLe.Args[0], asLe.Args[1]);
            }

            // BVUGT
            // !(x > y) ==> ( x <= y )
            var asBVUGT = ExprUtil.AsBVUGT(e);
            if (asBVUGT != null)
            {
                return this.BVULE(asBVUGT.Args[0], asBVUGT.Args[1]);
            }

            // BVUGE
            // !(x >= y) ==> ( x < y )
            var asBVUGE = ExprUtil.AsBVUGE(e);
            if (asBVUGE != null)
            {
                return this.BVULT(asBVUGE.Args[0], asBVUGE.Args[1]);
            }

            // BVULT
            // !(x < y) ==> ( x >= y )
            var asBVULT = ExprUtil.AsBVULT(e);
            if (asBVULT != null)
            {
                return this.BVUGE(asBVULT.Args[0], asBVULT.Args[1]);
            }

            // BVULE
            // !(x < y) ==> ( x >= y )
            var asBVULE = ExprUtil.AsBVULE(e);
            if (asBVULE != null)
            {
                return this.BVUGT(asBVULE.Args[0], asBVULE.Args[1]);
            }

            // BVSGT
            // !(x > y) ==> ( x <= y )
            var asBVSGT = ExprUtil.AsBVSGT(e);
            if (asBVSGT != null)
            {
                return this.BVSLE(asBVSGT.Args[0], asBVSGT.Args[1]);
            }

            // BVSGE
            // !(x >= y) ==> ( x < y )
            var asBVSGE = ExprUtil.AsBVSGE(e);
            if (asBVSGE != null)
            {
                return this.BVSLT(asBVSGE.Args[0], asBVSGE.Args[1]);
            }

            // BVSLT
            // !(x < y) ==> ( x >= y )
            var asBVSLT = ExprUtil.AsBVSLT(e);
            if (asBVSLT != null)
            {
                return this.BVSGE(asBVSLT.Args[0], asBVSLT.Args[1]);
            }

            // BVSLE
            // !(x < y) ==> ( x >= y )
            var asBVSLE = ExprUtil.AsBVSLE(e);
            if (asBVSLE != null)
            {
                return this.BVSGT(asBVSLE.Args[0], asBVSLE.Args[1]);
            }

            // Can't constant fold
            return UB.Not(e);
        }

        public override Expr Sub(Expr lhs, Expr rhs)
        {
            var lhsLit = ExprUtil.AsLiteral(lhs);
            var rhsLit = ExprUtil.AsLiteral(rhs);
            if (lhsLit != null && rhsLit != null)
            {
                Debug.Assert(lhs.Type.Equals(rhs.Type), "Mismatching types");
                if (lhsLit.isBigNum && rhsLit.isBigNum)
                {
                    // Int
                    return this.ConstantInt(( lhsLit.asBigNum - rhsLit.asBigNum ).ToBigInteger);
                }
                else if (lhsLit.isBigDec && rhsLit.isBigDec)
                {
                    // Real
                    return this.ConstantReal(lhsLit.asBigDec - rhsLit.asBigDec);
                }
                else
                    throw new NotSupportedException("Unsupported types in - constant fold");
            }

            // 0 - <expr> ==> -<expr>
            if (ExprUtil.IsZero(lhs))
            {
                return this.Neg(rhs);
            }

            // <expr> - 0 ==> <expr>
            if (ExprUtil.IsZero(rhs))
            {
                return lhs;
            }

            // <expr> - <constant>  ==> (-<constant>) + <expr>
            if (rhsLit != null)
            {
                return this.Add(this.Neg(rhsLit), lhs);
            }

            // <expr> - <expr> ==> 0
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                if (lhs.Type.IsInt)
                    return this.ConstantInt(0);
                else if (lhs.Type.IsReal)
                    return this.ConstantReal("0.0");
                else
                    throw new ExprTypeCheckException("lhs and rhs must both be of type real or int");
            }

            // Can't constant fold
            return UB.Sub(lhs, rhs);
        }

        /// <summary>
        /// Computes the euclidean div and mod.
        /// 
        /// Euclidean Division and mod are defined as follows (assuming n != 0)
        /// 
        /// q = m div n
        /// r = m mod n
        /// n*q + r = m
        /// 0 <= r < |n|
        ///
        /// This implementation is based on
        /// "Division and Modulus for Computer Scientists" by Daan Leijen
        /// http://research.microsoft.com/pubs/151917/divmodnote-letter.pdf
        ///
        /// It based on the assumption that "/" and "%" in C# perform "truncated division"
        /// </summary>
        /// <returns>Tuple, first item is the result of div and second item is result of mod</returns>
        /// <param name="n">Dividend/param>
        /// <param name="m">Divisor</param>
        private Tuple<BigInteger,BigInteger> ComputeEuclideanDivAndMod(BigInteger n, BigInteger m)
        {
            Debug.Assert(m != 0);
            var truncatedDiv = n / m;
            var truncatedMod = n % m;

            if (truncatedMod.IsZero || truncatedMod > 0)
                return Tuple.Create(truncatedDiv, truncatedMod);
            else
            {
                if (m > 0)
                    return Tuple.Create(truncatedDiv - 1, truncatedMod + m);
                else
                    return Tuple.Create(truncatedDiv + 1, truncatedMod - m);
            }
        }

        public override Expr Mod(Expr lhs, Expr rhs)
        {
            var litLhs = ExprUtil.AsLiteral(lhs);
            var litRhs = ExprUtil.AsLiteral(rhs);
            if (litLhs != null && litRhs != null)
            {
                if (!litLhs.isBigNum)
                    throw new ExprTypeCheckException("lhs must be int");

                if (!litRhs.isBigNum)
                    throw new ExprTypeCheckException("rhs must be int");

                var numerator = litLhs.asBigNum.ToBigInteger;
                var denominator = litRhs.asBigNum.ToBigInteger;

                // Can't do modulo by zero so check it's safe to compute first
                if (!denominator.IsZero)
                {
                    var computedValue = ComputeEuclideanDivAndMod(numerator, denominator);
                    return this.ConstantInt(computedValue.Item2);
                }
            }

            // can't constant fold
            return UB.Mod(lhs, rhs);
        }

        public override Expr Div(Expr lhs, Expr rhs)
        {
            var litLhs = ExprUtil.AsLiteral(lhs);
            var litRhs = ExprUtil.AsLiteral(rhs);
            if (litLhs != null && litRhs != null)
            {
                if (!litLhs.isBigNum)
                    throw new ExprTypeCheckException("lhs must be int");

                if (!litRhs.isBigNum)
                    throw new ExprTypeCheckException("rhs must be int");

                var numerator = litLhs.asBigNum.ToBigInteger;
                var denominator = litRhs.asBigNum.ToBigInteger;

                // Can't do modulo by zero so check it's safe to compute first
                if (!denominator.IsZero)
                {
                    var computedValue = ComputeEuclideanDivAndMod(numerator, denominator);
                    return this.ConstantInt(computedValue.Item1);
                }
            }

            // <expr> div 1 ==> <expr>
            if (litRhs != null)
            {
                if (litRhs.isBigNum)
                {
                    if (litRhs.asBigNum == BigNum.FromInt(1))
                    {
                        return lhs;
                    }
                }
            }

            // Cannot do
            // 0 div <expr> ==> 0
            // because we cannot guarantee that <expr> never evaluates
            // to zero value unless it's a constant (in which case
            // it's already evaluated by the case that handles when lhs and rhs
            // are constant.
            //
            // (declare-fun x () Int)
            // (declare-fun y () Int)
            // (assert (= x 0))
            // (assert (distinct 0 (div x y)))
            // (check-sat)
            // sat



            // ((a div b) div c) ==> (a div (b * c))
            //
            // Is this correct? Here's the SMTLIBv2 for it. Z3 doesn't return an answer though
            // (set-logic QF_NIA)
            // (declare-fun  a () Int)
            // (declare-fun  b () Int)
            // (declare-fun  c () Int)
            // (assert (not (= (div (div a b) c) (div a (* b c) ) ) ) )
            // (check-sat)
            //
            var lhsAsDiv = ExprUtil.AsDiv(lhs);
            if (lhsAsDiv != null)
            {
                if (!lhs.Type.IsInt || !rhs.Type.IsInt)
                    throw new ExprTypeCheckException("lhs and rhs must both be of type int");

                return this.Div(lhsAsDiv.Args[0], this.Mul(lhsAsDiv.Args[1], rhs));
            }

            // can't constant fold
            return UB.Div(lhs, rhs);
        }

        // Don't constant fold RealDiv, this will loose precision

        public override Expr And(Expr lhs, Expr rhs)
        {
            // And is commutative so to simplify code if there is a constant ensure
            // it is always on the left
            if (ExprUtil.AsLiteral(rhs) != null)
            {
                Expr temp = lhs;
                lhs = rhs;
                rhs = temp;
            }

            var litLhs = ExprUtil.AsLiteral(lhs);

            // false AND <expr> ==> false
            if (litLhs != null && ExprUtil.IsFalse(litLhs))
            {
                return this.False;
            }

            // true and <expr> ==> <expr>
            if (litLhs != null && ExprUtil.IsTrue(litLhs))
            {
                return rhs;
            }

            // <expr> and <expr> ==> <expr>
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                if (!lhs.Type.IsBool)
                {
                    throw new ExprTypeCheckException("arguments to And must be of bool type");
                }
                return lhs;
            }

            // Can't constant fold
            return UB.And(lhs, rhs);
        }

        public override Expr Or(Expr lhs, Expr rhs)
        {
            // Or is commutative so to simplify code if there is a constant ensure
            // it is always on the left
            if (ExprUtil.AsLiteral(rhs) != null)
            {
                Expr temp = lhs;
                lhs = rhs;
                rhs = temp;
            }

            var litLhs = ExprUtil.AsLiteral(lhs);

            // false OR <expr> ==> <expr>
            if (litLhs != null && ExprUtil.IsFalse(litLhs))
            {
                return rhs;
            }

            // true OR <expr> ==> true
            if (litLhs != null && ExprUtil.IsTrue(litLhs))
            {
                return this.True;
            }

            // <expr> OR <expr> ==> <expr>
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                if (!lhs.Type.IsBool)
                {
                    throw new ExprTypeCheckException("arguments to And must be of bool type");
                }
                return lhs;
            }

            // Can't constant fold
            return UB.Or(lhs, rhs);
        }

        public override Expr Imp(Expr lhs, Expr rhs)
        {
            var litLhs = ExprUtil.AsLiteral(lhs);
            if (litLhs != null)
            {
                if (!rhs.Type.IsBool)
                    throw new ExprTypeCheckException("rhs of implication must of bool type");

                if (litLhs.IsTrue)
                {
                    // true => <expr> ==> <expr>
                    return rhs;
                }
                else if (litLhs.IsFalse)
                {
                    // false => <expr> ==> true
                    return this.True;
                }
            }

            // <expr> => <expr> ===> true
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                return this.True;
            }

            // can't constant fold
            return UB.Imp(lhs, rhs);
        }

        public override Expr Iff(Expr lhs, Expr rhs)
        {
            // use commutativity to ensure if a constant exists that it's on the left
            if (ExprUtil.AsLiteral(rhs) != null)
            {
                Expr temp = lhs;
                lhs = rhs;
                rhs = temp;
            }

            var litLhs = ExprUtil.AsLiteral(lhs);


            if (litLhs != null)
            {
                if (litLhs.asBool)
                {
                    // (true <==> <expr>) ==> <expr>
                    return rhs;
                }
                else
                {
                    // (false <==> <expr>) ==> !<expr>
                    return this.Not(rhs);
                }
            }

            // (<expr> <==> <expr>) ==> true
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                return this.True;
            }

            // Can't constant fold
            return UB.Iff(lhs, rhs);
        }

        public override Expr Neg(Expr e)
        {
            var litArg = ExprUtil.AsLiteral(e);
            if (litArg != null)
            {
                if (litArg.isBigNum)
                {
                    // Int
                    var newValue = BigNum.FromBigInt(litArg.asBigNum.ToBigInteger * -1);
                    return this.ConstantInt(newValue.ToBigInteger);
                }
                else if (litArg.isBigDec)
                {
                    // Real
                    return this.ConstantReal(litArg.asBigDec.Negate);
                }
                else
                {
                    throw new NotSupportedException();
                }
            }

            // --<expr> ==> <expr>
            var negChild = ExprUtil.AsNeg(e);
            if (negChild != null)
            {
                return negChild.Args[0];
            }

            // Can't constant fold
            return UB.Neg(e);
        }

        public override Expr Lt(Expr lhs, Expr rhs)
        {
            var litLhs = ExprUtil.AsLiteral(lhs);
            var litRhs = ExprUtil.AsLiteral(rhs);
            if (litLhs != null && litRhs != null)
            {
                if (litLhs.isBigNum && litRhs.isBigNum)
                {
                    // Int
                    if (litLhs.asBigNum < litRhs.asBigNum)
                        return this.True;
                    else
                        return this.False;
                }
                else if (litLhs.isBigDec && litRhs.isBigDec)
                {
                    // Real
                    if (litLhs.asBigDec < litRhs.asBigDec)
                        return this.True;
                    else
                        return this.False;
                }
                else
                    throw new ExprTypeCheckException("lhs and rhs must both");
            }

            // <expr> < <expr> ==> false
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                return this.False;
            }

            // Can't constant fold
            return UB.Lt(lhs, rhs);
        }

        public override Expr Le(Expr lhs, Expr rhs)
        {
            var litLhs = ExprUtil.AsLiteral(lhs);
            var litRhs = ExprUtil.AsLiteral(rhs);
            if (litLhs != null && litRhs != null)
            {
                if (litLhs.isBigNum && litRhs.isBigNum)
                {
                    // Int
                    if (litLhs.asBigNum <= litRhs.asBigNum)
                        return this.True;
                    else
                        return this.False;
                }
                else if (litLhs.isBigDec && litRhs.isBigDec)
                {
                    // Real
                    if (litLhs.asBigDec <= litRhs.asBigDec)
                        return this.True;
                    else
                        return this.False;
                }
                else
                    throw new ExprTypeCheckException("lhs and rhs must both");
            }

            // <expr> <= <expr> ==> true
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                return this.True;
            }

            // Can't constant fold
            return UB.Le(lhs, rhs);
        }

        public override Expr Gt(Expr lhs, Expr rhs)
        {
            var litLhs = ExprUtil.AsLiteral(lhs);
            var litRhs = ExprUtil.AsLiteral(rhs);
            if (litLhs != null && litRhs != null)
            {
                if (litLhs.isBigNum && litRhs.isBigNum)
                {
                    // Int
                    if (litLhs.asBigNum > litRhs.asBigNum)
                        return this.True;
                    else
                        return this.False;
                }
                else if (litLhs.isBigDec && litRhs.isBigDec)
                {
                    // Real
                    if (litLhs.asBigDec > litRhs.asBigDec)
                        return this.True;
                    else
                        return this.False;
                }
                else
                    throw new ExprTypeCheckException("lhs and rhs must both");
            }

            // <expr> > <expr> ==> false
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                return this.False;
            }

            // Can't constant fold
            return UB.Gt(lhs, rhs);
        }

        public override Expr Ge(Expr lhs, Expr rhs)
        {
            var litLhs = ExprUtil.AsLiteral(lhs);
            var litRhs = ExprUtil.AsLiteral(rhs);
            if (litLhs != null && litRhs != null)
            {
                if (litLhs.isBigNum && litRhs.isBigNum)
                {
                    // Int
                    if (litLhs.asBigNum >= litRhs.asBigNum)
                        return this.True;
                    else
                        return this.False;
                }
                else if (litLhs.isBigDec && litRhs.isBigDec)
                {
                    // Real
                    if (litLhs.asBigDec >= litRhs.asBigDec)
                        return this.True;
                    else
                        return this.False;
                }
                else
                    throw new ExprTypeCheckException("lhs and rhs must both");
            }

            // <expr> >= <expr> ==> true
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                return this.True;
            }

            // Can't constant fold
            return UB.Ge(lhs, rhs);
        }

        public override Expr ForAll(IList<Variable> freeVars, Expr body, Trigger triggers=null)
        {
            var litBody = ExprUtil.AsLiteral(body);
            // (∀ x :: true) ==> true
            // (∀ x :: false) ==> false
            if (litBody != null)
            {
                return body;
            }

            // Can't constant fold
            return UB.ForAll(freeVars, body, triggers);
        }

        public override Expr Exists(IList<Variable> freeVars, Expr body, Trigger triggers=null)
        {
            var litBody = ExprUtil.AsLiteral(body);
            // (∃ x :: true) ==> true
            // (∃ x :: false) ==> false
            if (litBody != null)
            {
                return body;
            }

            // Can't constant fold
            return UB.Exists(freeVars, body, triggers);
        }

        private BigInteger MaxValuePlusOne(int bitWidth)
        {
            return BigInteger.One << bitWidth; // 2^(number of bits)
        }

        public override Expr BVADD(Expr lhs, Expr rhs)
        {
            // Ensure if there is a constant there will always be one of the left
            if (ExprUtil.AsLiteral(rhs) != null)
            {
                // Swap
                Expr temp = rhs;
                rhs = lhs;
                lhs = temp;
            }

            var litLhs = ExprUtil.AsLiteral(lhs);
            var litRhs = ExprUtil.AsLiteral(rhs);

            if (litLhs != null && litRhs != null)
            {
                if (!litLhs.Type.Equals(litRhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs must be bitvectors");

                if (!litLhs.isBvConst)
                    throw new ExprTypeCheckException("lhs and rhs must be bitvectors");

                // Compute bvand
                var maxValuePlusOne = MaxValuePlusOne(litLhs.asBvConst.Bits); // 2^( number of bits)
                var lhsBI = litLhs.asBvConst.Value.ToBigInteger;
                var rhsBI = litRhs.asBvConst.Value.ToBigInteger;
                var result = ( lhsBI + rhsBI ) % maxValuePlusOne; // Wrapping overflow
                return this.ConstantBV(result, litLhs.asBvConst.Bits);
            }

            // 0 + x ==> x
            if (ExprUtil.IsZero(lhs))
            {
                return rhs;
            }

            var rhsAsBVADD = ExprUtil.AsBVADD(rhs);
            if (rhsAsBVADD != null)
            {
                var rhsBVADDLeftLiteral = ExprUtil.AsLiteral(rhsAsBVADD.Args[0]);
                if (rhsBVADDLeftLiteral != null)
                {
                    if (litLhs != null)
                    {
                        //     +
                        //    / \
                        //   1   +
                        //      / \
                        //     2  x
                        // fold to
                        // 2 + x
                        var result = this.BVADD(litLhs, rhsBVADDLeftLiteral);
                        return this.BVADD(result, rhsAsBVADD.Args[1]);
                    }
                    else
                    {
                        //     +
                        //    / \
                        //   x   +
                        //      / \
                        //     1  y
                        // propagate constant up
                        //     +
                        //    / \
                        //   1   +
                        //      / \
                        //     x  y
                        var newSubExprBVADD = this.BVADD(lhs, rhsAsBVADD.Args[1]);
                        return this.BVADD(rhsBVADDLeftLiteral, newSubExprBVADD);
                    }
                }
            }

            // x + x ==> 2* x
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                return this.BVMUL(this.ConstantBV(2, lhs.Type.BvBits), lhs);
            }

            // Can't constant fold
            return UB.BVADD(lhs, rhs);
        }

        public override Expr BVSUB(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
                throw new ExprTypeCheckException("lhs and rhs must be bitvectors");

            if (!lhs.Type.IsBv)
                throw new ExprTypeCheckException("lhs and rhs must be bitvectors");

            var litLhs = ExprUtil.AsLiteral(lhs);
            var litRhs = ExprUtil.AsLiteral(rhs);

            if (litLhs != null && litRhs != null)
            {
                // Compute bvand
                var maxValuePlusOne = MaxValuePlusOne(litLhs.asBvConst.Bits); // 2^( number of bits)
                var lhsBI = litLhs.asBvConst.Value.ToBigInteger;
                var rhsBI = litRhs.asBvConst.Value.ToBigInteger;
                var result = ( lhsBI - rhsBI ) % maxValuePlusOne; // Wrapping overflow
                return this.ConstantBV(result, litLhs.asBvConst.Bits);
            }

            // <expr> - 0 ==> <expr>
            if (ExprUtil.IsZero(rhs))
            {
                return lhs;
            }

            // 0 - <expr> ==> (bvneg <expr>)
            if (ExprUtil.IsZero(lhs))
            {
                return BVNEG(rhs);
            }

            // <expr> - <expr> ==> 0
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                return ConstantBV(0, lhs.Type.BvBits);
            }

            return UB.BVSUB(lhs, rhs);
        }


        public override Expr BVMUL(Expr lhs, Expr rhs)
        {
            // Ensure if there is a constant there will always be one of the left
            if (ExprUtil.AsLiteral(rhs) != null)
            {
                // Swap
                Expr temp = rhs;
                rhs = lhs;
                lhs = temp;
            }

            var litLhs = ExprUtil.AsLiteral(lhs);
            var litRhs = ExprUtil.AsLiteral(rhs);

            if (litLhs != null && litRhs != null)
            {
                if (!litLhs.Type.Equals(litRhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs must be bitvectors");

                if (!litLhs.isBvConst)
                    throw new ExprTypeCheckException("lhs and rhs must be bitvectors");

                // Compute bvand
                var maxValuePlusOne = MaxValuePlusOne(litLhs.asBvConst.Bits); // 2^( number of bits)
                var lhsBI = litLhs.asBvConst.Value.ToBigInteger;
                var rhsBI = litRhs.asBvConst.Value.ToBigInteger;
                var result = ( lhsBI * rhsBI ) % maxValuePlusOne; // Wrapping overflow
                return this.ConstantBV(result, litLhs.asBvConst.Bits);
            }

            // 0 * x ==> 0
            if (ExprUtil.IsZero(lhs))
            {
                return this.ConstantBV(0, lhs.Type.BvBits);
            }

            var rhsAsBVMUL = ExprUtil.AsBVMUL(rhs);
            if (rhsAsBVMUL != null)
            {
                var rhsBVMULLeftLiteral = ExprUtil.AsLiteral(rhsAsBVMUL.Args[0]);
                if (rhsBVMULLeftLiteral != null)
                {
                    if (litLhs != null)
                    {
                        //     *
                        //    / \
                        //   1   *
                        //      / \
                        //     2  x
                        // fold to
                        // 2 + x
                        var result = this.BVMUL(litLhs, rhsBVMULLeftLiteral);
                        return this.BVMUL(result, rhsAsBVMUL.Args[1]);
                    }
                    else
                    {
                        //     *
                        //    / \
                        //   x   *
                        //      / \
                        //     1  y
                        // propagate constant up
                        //     *
                        //    / \
                        //   1   *
                        //      / \
                        //     x  y
                        var newSubExprBVADD = this.BVMUL(lhs, rhsAsBVMUL.Args[1]);
                        return this.BVMUL(rhsBVMULLeftLiteral, newSubExprBVADD);
                    }
                }
            }
                

            // Can't constant fold
            return UB.BVMUL(lhs, rhs);
        }

        public override Expr BVUDIV(Expr lhs, Expr rhs)
        {
            // FIXME: I'm not sure about this, we're potentially type checking all Expr twice by doing this (here and in UB)
            if (!lhs.Type.Equals(rhs.Type))
                throw new ExprTypeCheckException("lhs and rhs type must be the same type");

            if (!lhs.Type.IsBv)
                throw new ExprTypeCheckException("arguments must be of bv type");

            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);


            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (rhsAsLit.asBvConst.Value.IsZero)
                {
                    // Can't divide by zero, don't fold
                    return UB.BVUDIV(lhs, rhs);
                }

                //    [[(bvudiv s t)]] := if bv2nat([[t]]) != 0 then
                //                           nat2bv[m](bv2nat([[s]]) div bv2nat([[t]]))
                //
                var maxValuePlusOne = MaxValuePlusOne(lhsAsLit.asBvConst.Bits); // 2^( number of bits)
                Debug.Assert(!lhsAsLit.asBvConst.Value.IsNegative);
                Debug.Assert(!rhsAsLit.asBvConst.Value.IsNegative);
                var result = ( lhsAsLit.asBvConst.Value.ToBigInteger / rhsAsLit.asBvConst.Value.ToBigInteger ) % maxValuePlusOne;
                return ConstantBV(result, lhsAsLit.asBvConst.Bits);
            }

            // x / 1 ==> x
            //
            // (declare-fun x () (_ BitVec 8))
            // (declare-fun y () (_ BitVec 8))
            // (assert (= y (_ bv1 8)))
            // (assert (distinct x (bvudiv x y)))
            // (check-sat)
            // unsat
            if (rhsAsLit != null && ExprUtil.IsOne(rhsAsLit))
            {
                return lhs;
            }

            return UB.BVUDIV(lhs, rhs);
        }

        public override Expr BVUREM(Expr lhs, Expr rhs)
        {
            // FIXME: I'm not sure about this, we're potentially type checking all Expr twice by doing this (here and in UB)
            if (!lhs.Type.Equals(rhs.Type))
                throw new ExprTypeCheckException("lhs and rhs type must be the same type");

            if (!lhs.Type.IsBv)
                throw new ExprTypeCheckException("arguments must be of bv type");

            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);

            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (rhsAsLit.asBvConst.Value.IsZero)
                {
                    // Can't divide by zero, don't fold
                    return UB.BVUREM(lhs, rhs);
                }


                var maxValuePlusOne = MaxValuePlusOne(lhsAsLit.asBvConst.Bits); // 2^( number of bits)
                Debug.Assert(!lhsAsLit.asBvConst.Value.IsNegative);
                Debug.Assert(!rhsAsLit.asBvConst.Value.IsNegative);
                var result = ( lhsAsLit.asBvConst.Value.ToBigInteger % rhsAsLit.asBvConst.Value.ToBigInteger ) % maxValuePlusOne;
                return ConstantBV(result, lhsAsLit.asBvConst.Bits);
            }

            // x % 1 ==> 0
            //
            // (declare-fun x () (_ BitVec 8))
            // (declare-fun y () (_ BitVec 8))
            // (assert (= y (_ bv1 8)))
            // (assert (distinct (_ bv0 8) (bvurem x y)))
            // (check-sat)
            // unsat
            if (ExprUtil.IsOne(rhs))
            {
                return ConstantBV(0, rhs.Type.BvBits);
            }

            return UB.BVUREM(lhs, rhs);
        }

        private BigInteger BvNegOnNaturalNumber(BigInteger value, int bitwidth)
        {
            var maxValuePlusOne = MaxValuePlusOne(bitwidth); // 2^( number of bits)
            return ( maxValuePlusOne - value ) % maxValuePlusOne;
        }

        public override Expr BVSDIV(Expr lhs, Expr rhs)
        {
            // FIXME: I'm not sure about this, we're potentially type checking all Expr twice by doing this (here and in UB)
            if (!lhs.Type.Equals(rhs.Type))
                throw new ExprTypeCheckException("lhs and rhs type must be the same type");

            if (!lhs.Type.IsBv)
                throw new ExprTypeCheckException("arguments must be of bv type");

            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                var numerator = lhsAsLit;
                var denominator = rhsAsLit;

                if (denominator.asBvConst.Value.IsZero)
                {
                    // Can't divide by zero, don't fold
                    return UB.BVSDIV(lhs, rhs);
                }

                // (bvsdiv s t) abbreviates
                // (let ((?msb_s ((_ extract |m-1| |m-1|) s))
                // (?msb_t ((_ extract |m-1| |m-1|) t)))
                // (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
                // (bvudiv s t)
                // (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
                // (bvneg (bvudiv (bvneg s) t))
                // (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
                // (bvneg (bvudiv s (bvneg t)))
                // (bvudiv (bvneg s) (bvneg t))))))

                // Check the sign of the bitvector in a two's complement representation
                int bitwidth = numerator.asBvConst.Bits;
                var threshold = BigInteger.Pow(2, bitwidth - 1);


                bool numeratorIsPositiveOrZero = numerator.asBvConst.Value.ToBigInteger < threshold;
                bool denominatorIsPositiveOrZero = denominator.asBvConst.Value.ToBigInteger < threshold;

                BigInteger result=0;

                if (numeratorIsPositiveOrZero && denominatorIsPositiveOrZero)
                {
                    result = numerator.asBvConst.Value.ToBigInteger /
                        denominator.asBvConst.Value.ToBigInteger;
                }
                else if (!numeratorIsPositiveOrZero && denominatorIsPositiveOrZero)
                {
                    result = BvNegOnNaturalNumber(
                        BvNegOnNaturalNumber(numerator.asBvConst.Value.ToBigInteger, bitwidth) /
                        denominator.asBvConst.Value.ToBigInteger,
                        bitwidth
                    );
                }
                else if (numeratorIsPositiveOrZero && !denominatorIsPositiveOrZero)
                {
                    result = BvNegOnNaturalNumber(
                        numerator.asBvConst.Value.ToBigInteger /
                        BvNegOnNaturalNumber(denominator.asBvConst.Value.ToBigInteger, bitwidth ),
                        bitwidth
                    );
                }
                else
                {
                    Debug.Assert(!numeratorIsPositiveOrZero && !denominatorIsPositiveOrZero);
                    result = BvNegOnNaturalNumber(numerator.asBvConst.Value.ToBigInteger, bitwidth) /
                        BvNegOnNaturalNumber(denominator.asBvConst.Value.ToBigInteger, bitwidth);
                }

                Debug.Assert(result >= 0);
                return ConstantBV(result, numerator.asBvConst.Bits);
            }

            // x / 1 ==> x
            //
            // (declare-fun x () (_ BitVec 8))
            // (declare-fun y () (_ BitVec 8))
            // (assert (= y (_ bv1 8)))
            // (assert (distinct x (bvsdiv x y)))
            // (check-sat)
            // unsat
            if (ExprUtil.IsOne(rhs))
            {
                return lhs;
            }

            return UB.BVSDIV(lhs, rhs);
        }

        public override Expr BVSREM(Expr lhs, Expr rhs)
        {
            // FIXME: I'm not sure about this, we're potentially type checking all Expr twice by doing this (here and in UB)
            if (!lhs.Type.Equals(rhs.Type))
                throw new ExprTypeCheckException("lhs and rhs type must be the same type");

            if (!lhs.Type.IsBv)
                throw new ExprTypeCheckException("arguments must be of bv type");

            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                var numerator = lhsAsLit;
                var denominator = rhsAsLit;
                Debug.Assert(numerator.isBvConst);
                Debug.Assert(denominator.isBvConst);
                Debug.Assert(numerator .asBvConst.Bits == denominator.asBvConst.Bits);

                // 2's complement signed remainder (sign follows dividend)
                //
                //     (bvsrem s t) abbreviates
                // (let ((?msb_s ((_ extract |m-1| |m-1|) s))
                // (?msb_t ((_ extract |m-1| |m-1|) t)))
                // (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
                //   (bvurem s t)
                // (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
                //   (bvneg (bvurem (bvneg s) t))
                // (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
                //   (bvurem s (bvneg t)))
                // (bvneg (bvurem (bvneg s) (bvneg t))))))

                if (denominator.asBvConst.Value.IsZero)
                {
                    // Can't divide by zero, don't fold
                    return UB.BVSREM(lhs, rhs);
                }

                // Check the sign of the bitvector in a two's complement representation
                int bitwidth = numerator.asBvConst.Bits;
                var threshold = BigInteger.Pow(2, bitwidth - 1);
                var maxValuePlusOne = MaxValuePlusOne(bitwidth); // 2^( number of bits)

                bool numeratorIsPositiveOrZero = numerator.asBvConst.Value.ToBigInteger < threshold;
                bool denominatorIsPositiveOrZero = denominator.asBvConst.Value.ToBigInteger < threshold;

                BigInteger result=0;

                if (numeratorIsPositiveOrZero && denominatorIsPositiveOrZero)
                {
                    result = (numerator.asBvConst.Value.ToBigInteger %
                              denominator.asBvConst.Value.ToBigInteger) % maxValuePlusOne;
                }
                else if (!numeratorIsPositiveOrZero && denominatorIsPositiveOrZero)
                {
                    result = BvNegOnNaturalNumber(
                        BvNegOnNaturalNumber(numerator.asBvConst.Value.ToBigInteger, bitwidth) %
                        denominator.asBvConst.Value.ToBigInteger,
                        bitwidth
                    ) % maxValuePlusOne;
                }
                else if (numeratorIsPositiveOrZero && !denominatorIsPositiveOrZero)
                {
                    result = (
                        numerator.asBvConst.Value.ToBigInteger %
                        BvNegOnNaturalNumber(denominator.asBvConst.Value.ToBigInteger, bitwidth )
                    ) % maxValuePlusOne;
                }
                else
                {
                    Debug.Assert(!numeratorIsPositiveOrZero && !denominatorIsPositiveOrZero);
                    result = BvNegOnNaturalNumber(( BvNegOnNaturalNumber(numerator.asBvConst.Value.ToBigInteger, bitwidth) %
                                                   BvNegOnNaturalNumber(denominator.asBvConst.Value.ToBigInteger, bitwidth) ) % maxValuePlusOne, bitwidth);
                }

                Debug.Assert(result >= 0);
                return ConstantBV(result, bitwidth);
            }

            // x % 1 ==> 0
            //
            // (declare-fun x () (_ BitVec 8))
            // (declare-fun y () (_ BitVec 8))
            // (assert (= y (_ bv1 8)))
            // (assert (distinct (_ bv0 8) (bvsrem x y)))
            // (check-sat)
            // unsat
            if (ExprUtil.IsOne(rhs))
            {
                return ConstantBV(0, rhs.Type.BvBits);
            }


            return UB.BVSREM(lhs, rhs);
        }

        public override Expr BVSMOD(Expr lhs, Expr rhs)
        {
            // FIXME: I'm not sure about this, we're potentially type checking all Expr twice by doing this (here and in UB)
            if (!lhs.Type.Equals(rhs.Type))
                throw new ExprTypeCheckException("lhs and rhs type must be the same type");

            if (!lhs.Type.IsBv)
                throw new ExprTypeCheckException("arguments must be of bv type");

            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                // SMTLIBv2 definition
                // 2's complement signed remainder (sign follows divisor)
                //
                //    (bvsmod s t) abbreviates
                // (let ((?msb_s ((_ extract |m-1| |m-1|) s))
                //       (?msb_t ((_ extract |m-1| |m-1|) t)))
                //       (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
                //             (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
                //             (let ((u (bvurem abs_s abs_t)))
                //                  (ite (= u (_ bv0 m))
                //                       u
                //                       (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
                //                             u
                //                             (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
                //                                  (bvadd (bvneg u) t)
                //                                  (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
                //                                  (bvadd u t)
                //                                  (bvneg u))))))))

                var numerator = lhsAsLit.asBvConst;
                var denominator = rhsAsLit.asBvConst;
                int bitWidth = numerator.Bits;
                Debug.Assert(numerator.Bits == denominator.Bits);
                Debug.Assert(!numerator.Value.IsNegative);
                Debug.Assert(!denominator.Value.IsNegative);

                if (denominator.Value.IsZero)
                {
                    // Can't do bvsmod by zero so don't fold
                    return UB.BVSMOD(lhs, rhs);
                }

                var threshold = BigInteger.Pow(2, bitWidth - 1);
                var numeratorIsPositiveOrZero = numerator.Value.ToBigInteger < threshold;
                var denominatorIsPositiveOrZero = denominator.Value.ToBigInteger < threshold;

                BigInteger absNumerator = 0;

                // Compute the absolute value represented by the bitvector
                if (numeratorIsPositiveOrZero)
                    absNumerator = numerator.Value.ToBigInteger;
                else
                    absNumerator = BvNegOnNaturalNumber(numerator.Value.ToBigInteger, bitWidth);

                BigInteger absDenominator = 0;

                if (denominatorIsPositiveOrZero)
                    absDenominator = denominator.Value.ToBigInteger;
                else
                    absDenominator = BvNegOnNaturalNumber(denominator.Value.ToBigInteger, bitWidth);

                // Compute (bvurem absNumerator absDenominator). This corresponds to "u" in the SMTLIBv2 definition
                Debug.Assert(absNumerator >= 0);
                Debug.Assert(absDenominator >= 0);

                var bvuremAbsArgs = absNumerator % absDenominator;
                var maxValuePlusOne = BigInteger.Pow(2, bitWidth);

                BigInteger result = 0;
                if (bvuremAbsArgs.IsZero)
                {
                    result = 0;
                }
                else if (numeratorIsPositiveOrZero && denominatorIsPositiveOrZero)
                {
                    result = bvuremAbsArgs;
                }
                else if (!numeratorIsPositiveOrZero && denominatorIsPositiveOrZero)
                {
                    // (bvadd (bvneg u) t)
                    var bvNegU = BvNegOnNaturalNumber(bvuremAbsArgs, bitWidth);
                    result = ( bvNegU + denominator.Value.ToBigInteger ) % maxValuePlusOne;
                }
                else if (numeratorIsPositiveOrZero && !denominatorIsPositiveOrZero)
                {
                    //  (bvadd u t)
                    result = (bvuremAbsArgs + denominator.Value.ToBigInteger) % maxValuePlusOne;
                }
                else
                {
                    Debug.Assert(!numeratorIsPositiveOrZero && !denominatorIsPositiveOrZero);
                    result = BvNegOnNaturalNumber(bvuremAbsArgs, bitWidth);
                }

                return ConstantBV(result, bitWidth);
            }

            // x % 1 ==> 0
            //
            // (declare-fun x () (_ BitVec 8))
            // (declare-fun y () (_ BitVec 8))
            // (assert (= y (_ bv1 8)))
            // (assert (distinct (_ bv0 8) (bvsmod x y)))
            // (check-sat)
            // unsat
            if (ExprUtil.IsOne(rhs))
            {
                return ConstantBV(0, rhs.Type.BvBits);
            }

            return UB.BVSMOD(lhs, rhs);
        }

        public override Expr BVNEG(Expr operand)
        {
            var asLit = ExprUtil.AsLiteral(operand);
            if (asLit != null)
            {
                if (!asLit.isBvConst)
                    throw new ExprTypeCheckException("operand must be of bitvector type");

                return ConstantBV(BvNegOnNaturalNumber(asLit.asBvConst.Value.ToBigInteger, asLit.asBvConst.Bits), asLit.asBvConst.Bits);
            }

            // - (- x) ==> x
            //
            // (declare-fun x () (_ BitVec 4))
            // (assert (distinct x (bvneg (bvneg x))))
            // (check-sat)
            // unsat
            var asBvNeg = ExprUtil.AsBVNEG(operand);
            if (asBvNeg != null)
            {
                return asBvNeg.Args[0];
            }

            return UB.BVNEG(operand);
        }

        private BigInteger InvertDecimalReprBVBits(BigInteger decimalRepr, int bitWidth)
        {
            Debug.Assert(bitWidth > 0);
            var bitMask = BigInteger.Pow(2, bitWidth) -1; // Decimal representation of all ones
            var result = decimalRepr ^ bitMask; // Using Xor with all ones will invert all the bits
            return result;
        }

        public override Expr BVNOT(Expr operand)
        {
            var asLit = ExprUtil.AsLiteral(operand);
            if (asLit != null)
            {
                var result = InvertDecimalReprBVBits(asLit.asBvConst.Value.ToBigInteger, asLit.asBvConst.Bits);
                return ConstantBV(result, asLit.asBvConst.Bits);
            }

            // ~ (~x) ==> x
            //
            // (declare-fun x () (_ BitVec 8))
            // (assert (distinct x (bvnot (bvnot x))))
            // (check-sat)
            // unsat
            var asBvNot = ExprUtil.AsBVNOT(operand);
            if (asBvNot != null)
            {
                return asBvNot.Args[0];
            }

            return UB.BVNOT(operand);
        }

        public override Expr BVSEXT(Expr operand, int newWidth)
        {
            var asLit = ExprUtil.AsLiteral(operand);
            if (asLit != null)
            {
                if (newWidth < asLit.asBvConst.Bits)
                    throw new ExprTypeCheckException("Can't extend bitvector to a small length");

                if (newWidth == asLit.asBvConst.Bits)
                {
                    // Not doing any extending so just return the literal
                    return operand;
                }

                // Check the sign of the bitvector in a two's complement representation
                var threshold = BigInteger.Pow(2, asLit.asBvConst.Bits - 1);

                if (asLit.asBvConst.Value.ToBigInteger < threshold)
                {
                    // The bitvector is a positive bitvector under two's complement interpretation
                    // So sign extend does not change internal representation
                    return ConstantBV(asLit.asBvConst.Value.ToBigInteger, newWidth);
                }
                else
                {
                    // The bitvector is a negative bitvector under two's complement interpretation
                    // So we need to change the internal representation

                    // One way of looking at this as follows. Let x be the natural number representing
                    // the negative bitvector where m is the original bitvector width n is the new width
                    //
                    // 1. Compute the positive version of the bitvector which is (2^m - x) mod m
                    // 2. Sign extend that (which changes nothing)
                    // 3. Now negate again
                    //
                    // So the natural number representation of a bitvector of length n extend from a bitvector
                    // of length m is given by (assuming the bitvector was originally negative)
                    //
                    // (2^n - ((2^m -x) mod m)) mod n
                    //
                    // The mods are only for the case where x is zero so can drop those and have
                    // 2^n - 2^m + x

                    var maxNewPlusOne = BigInteger.Pow(2, newWidth);
                    var maxOldPlusOne = BigInteger.Pow(2, asLit.asBvConst.Bits);
                    var result = (maxNewPlusOne - maxOldPlusOne) + asLit.asBvConst.Value.ToBigInteger;
                    return ConstantBV(result, newWidth);
                }
            }

            // Sign extending to the same as the curent size is a no-op
            var asBvSExt = ExprUtil.AsBVSEXT(operand);
            if (asBvSExt != null)
            {
                var operandWidth = asBvSExt.ShallowType.BvBits;
                if (operandWidth == newWidth)
                    return operand;
            }

            return UB.BVSEXT(operand, newWidth);
        }

        public override Expr BVZEXT(Expr operand, int newWidth)
        {
            var asLit = ExprUtil.AsLiteral(operand);
            if (asLit != null)
            {
                if (newWidth < asLit.asBvConst.Bits)
                    throw new ExprTypeCheckException("Can't extend bitvector to a smaller length");

                if (newWidth == asLit.asBvConst.Bits)
                {
                    // Not doing any extending so just return the literal
                    return operand;
                }

                // Zero extend is very simple, we just make a wider bitvector with the same natural number representation
                return ConstantBV(asLit.asBvConst.Value.ToBigInteger, newWidth);
            }

            // BVZEXT(BVZEXT(<expr>)) ==> BVZEXT(<expr>)
            var asBvZExt = ExprUtil.AsBVZEXT(operand);
            if (asBvZExt != null)
            {
                var operandWidth = asBvZExt.ShallowType.BvBits;

                // Sign extending to the same width is a no-op
                if (operandWidth == newWidth)
                    return operand;

                if (newWidth < operandWidth)
                    throw new ExprTypeCheckException("Can't extend bitvector to a smaller length");

                return UB.BVZEXT(asBvZExt.Args[0], newWidth);
            }

            return UB.BVZEXT(operand, newWidth);
        }

        public override Expr BVCONCAT(Expr MSB, Expr LSB)
        {
            var asLitMSB = ExprUtil.AsLiteral(MSB);
            var asLitLSB = ExprUtil.AsLiteral(LSB);

            if (!MSB.Type.IsBv || !LSB.Type.IsBv)
                throw new ExprTypeCheckException("Both MSB and LSB must be of bitvector type");

            if (asLitMSB != null && asLitLSB != null)
            {
                var MSBBV = asLitMSB.asBvConst;
                var LSBBV = asLitLSB.asBvConst;

                // Compute concatenation
                BigInteger MSBShifted = MSBBV.Value.ToBigInteger << LSBBV.Bits;
                BigInteger resultAsBigInt = MSBShifted + LSBBV.Value.ToBigInteger;
                return ConstantBV(resultAsBigInt, MSBBV.Bits + LSBBV.Bits);
            }

            // CONCAT( 0bvX, <expr>) ==> BVZEXT(<expr>, newWidth)
            if (asLitMSB != null && ExprUtil.IsZero(asLitMSB))
            {
                var newWidth = MSB.Type.BvBits + LSB.Type.BvBits;
                return BVZEXT(LSB, newWidth);
            }

            // CONCAT( <expr>, 0bvX) == > BVSHL(BVZEXT(<expr>, newWidth), X)
            // Above is another transformation that could be applied if lsb is zero
            // but this wouldn't really simplify things so don't do it.


            // <expr>[a:z] ++ <expr>[z:c] ==> <expr>[a:c]
            //
            // If concatenating two BvExtractExpr whose ranges join
            // and the <expr> is the same then we can simplify to a single BvExtractExpr
            var msbAsBvExtract = ExprUtil.AsBVEXTRACT(MSB);
            var lsbAsBvExtract = ExprUtil.AsBVEXTRACT(LSB);
            if (msbAsBvExtract != null && lsbAsBvExtract != null && msbAsBvExtract.Start == lsbAsBvExtract.End)
            {
                if (ExprUtil.StructurallyEqual(msbAsBvExtract.Bitvector, lsbAsBvExtract.Bitvector))
                {
                    return BVEXTRACT(msbAsBvExtract.Bitvector, msbAsBvExtract.End, lsbAsBvExtract.Start);
                }
            }



            // Can't constant fold
            return UB.BVCONCAT(MSB, LSB);
        }

        public override Expr BVEXTRACT(Expr operand, int end, int start)
        {
            var asLit = ExprUtil.AsLiteral(operand);
            if (asLit != null)
            {
                // FIXME: We've just reimplemented the type checking in the SimpleExprBuilder
                if (!operand.Type.IsBv)
                    throw new ExprTypeCheckException("operand must be a bitvector");

                if (end < 0)
                    throw new ExprTypeCheckException("end must be >= 0");

                if (end <= start)
                    throw new ExprTypeCheckException("end must be > start");


                var BV = asLit.asBvConst;
                // ABitVector[<end>:<start>]
                // This operation selects bits starting at <start> to <end> but not including <end>

                // Compute the bit extraction
                BigInteger bitsBeforeStartRemoved = BV.Value.ToBigInteger >> start;
                int numberOfBitsInResult = end - start;
                BigInteger bitMask = (BigInteger.One << numberOfBitsInResult) -1;
                BigInteger result = bitsBeforeStartRemoved & bitMask; // Mask off bits we don't want
                return ConstantBV(result, numberOfBitsInResult);
            }

            // If end and start just select the whole bitvector
            // then is operation is a no-op
            if (operand.Type.IsBv && start == 0 && end == operand.Type.BvBits)
            {
                return operand;
            }


            // Check for trying extract a region with an extracted region.
            // We can recompute the effective end and start so there
            // is a single BvExtractExpr rather than two nested BvExtractExpr
            var operandAsBvExtract = ExprUtil.AsBVEXTRACT(operand);
            if (operand.Type.IsBv && operandAsBvExtract != null)
            {
                var originalEnd = operandAsBvExtract.End;
                var originalStart = operandAsBvExtract.Start;

                var effectiveStart = start + originalStart;
                var effectiveEnd = end + originalStart;

                if (effectiveEnd > originalEnd)
                    throw new ExprTypeCheckException("end is too large");

                return UB.BVEXTRACT(operandAsBvExtract.Bitvector, effectiveEnd, effectiveStart);
            }

            return UB.BVEXTRACT(operand, end, start);
        }

        public override Expr BVSLT(Expr lhs, Expr rhs)
        {
            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!lhs.Type.IsBv)
                    throw new ExprTypeCheckException("lhs must be a bitvector");


                // Check the sign of the bitvectors in a two's complement representation
                var threshold = BigInteger.Pow(2, lhsAsLit.asBvConst.Bits - 1);

                bool lhsIsPositiveOrZero = lhsAsLit.asBvConst.Value.ToBigInteger < threshold;
                bool rhsIsPositiveOrZero = rhsAsLit.asBvConst.Value.ToBigInteger < threshold;

                if (lhsIsPositiveOrZero == rhsIsPositiveOrZero)
                {
                    // For this case with twos complement representation
                    //
                    // Notation: (x+ve) means x where x is a positive or zero bitvector under two's complement
                    //  _decimal_rep means the decimal representation of the bitvector treating it as unsigned
                    //
                    //
                    // (x+ve) < (y+ve) == (x_decimal_rep) < (y_decimal_rep)
                    // (x-ve) < (y-ve) == (x_decimal_rep) < (y_decimal_rep)
                    return ConstantBool(lhsAsLit.asBvConst.Value < rhsAsLit.asBvConst.Value);
                }
                else if (lhsIsPositiveOrZero && !rhsIsPositiveOrZero)
                {
                    // (x+ve) < (y-ve) == False
                    return this.False;
                }
                else if (!lhsIsPositiveOrZero && rhsIsPositiveOrZero)
                {
                    // (x-ve) < (y+ve) == True
                    return this.True;
                }
                else
                {
                    throw new InvalidProgramException("Unreachable!");
                }
            }

            // <expr> < <expr> ==> false
            //
            // (declare-fun x () (_ BitVec 4))
            // (declare-fun y () (_ BitVec 4))
            // (assert (= x y))
            // (assert (distinct false (bvslt x y)))
            // (check-sat)
            // unsat
            if (ExprUtil.StructurallyEqual(lhs, rhs))
                return this.False;

            return UB.BVSLT(lhs, rhs);
        }

        public override Expr BVSLE(Expr lhs, Expr rhs)
        {
            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!lhs.Type.IsBv)
                    throw new ExprTypeCheckException("lhs must be a bitvector");


                // Check the sign of the bitvectors in a two's complement representation
                var threshold = BigInteger.Pow(2, lhsAsLit.asBvConst.Bits - 1);

                bool lhsIsPositiveOrZero = lhsAsLit.asBvConst.Value.ToBigInteger < threshold;
                bool rhsIsPositiveOrZero = rhsAsLit.asBvConst.Value.ToBigInteger < threshold;

                if (lhsIsPositiveOrZero == rhsIsPositiveOrZero)
                {
                    // For this case with twos complement representation
                    //
                    // Notation: (x+ve) means x where x is a positive or zero bitvector under two's complement
                    //  _decimal_rep means the decimal representation of the bitvector treating it as unsigned
                    //
                    //
                    // (x+ve) <= (y+ve) == (x_decimal_rep) <= (y_decimal_rep)
                    // (x-ve) <= (y-ve) == (x_decimal_rep) <= (y_decimal_rep)
                    return ConstantBool(lhsAsLit.asBvConst.Value <= rhsAsLit.asBvConst.Value);
                }
                else if (lhsIsPositiveOrZero && !rhsIsPositiveOrZero)
                {
                    // (x+ve) <= (y-ve) == False
                    return this.False;
                }
                else if (!lhsIsPositiveOrZero && rhsIsPositiveOrZero)
                {
                    // (x-ve) <= (y+ve) == True
                    return this.True;
                }
                else
                {
                    throw new InvalidProgramException("Unreachable!");
                }
            }

            // <expr> <= <expr> ==> true
            //
            // (declare-fun x () (_ BitVec 4))
            // (declare-fun y () (_ BitVec 4))
            // (assert (= x y))
            // (assert (distinct true (bvsle x y)))
            // (check-sat)
            // unsat
            if (ExprUtil.StructurallyEqual(lhs, rhs))
                return this.True;

            return UB.BVSLE(lhs, rhs);
        }

        public override Expr BVSGT(Expr lhs, Expr rhs)
        {
            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!lhs.Type.IsBv)
                    throw new ExprTypeCheckException("lhs must be a bitvector");


                // Check the sign of the bitvectors in a two's complement representation
                var threshold = BigInteger.Pow(2, lhsAsLit.asBvConst.Bits - 1);

                bool lhsIsPositiveOrZero = lhsAsLit.asBvConst.Value.ToBigInteger < threshold;
                bool rhsIsPositiveOrZero = rhsAsLit.asBvConst.Value.ToBigInteger < threshold;

                if (lhsIsPositiveOrZero == rhsIsPositiveOrZero)
                {
                    // For this case with twos complement representation
                    //
                    // Notation: (x+ve) means x where x is a positive or zero bitvector under two's complement
                    //  _decimal_rep means the decimal representation of the bitvector treating it as unsigned
                    //
                    //
                    // (x+ve) > (y+ve) == (x_decimal_rep) > (y_decimal_rep)
                    // (x-ve) > (y-ve) == (x_decimal_rep) > (y_decimal_rep)
                    return ConstantBool(lhsAsLit.asBvConst.Value > rhsAsLit.asBvConst.Value);
                }
                else if (lhsIsPositiveOrZero && !rhsIsPositiveOrZero)
                {
                    // (x+ve) > (y-ve) == True
                    return this.True;
                }
                else if (!lhsIsPositiveOrZero && rhsIsPositiveOrZero)
                {
                    // (x-ve) > (y+ve) == False
                    return this.False;
                }
                else
                {
                    throw new InvalidProgramException("Unreachable!");
                }
            }

            // <expr> > <expr> ==> false
            //
            // (declare-fun x () (_ BitVec 4))
            // (declare-fun y () (_ BitVec 4))
            // (assert (= x y))
            // (assert (distinct false (bvsgt x y)))
            // (check-sat)
            // unsat
            if (ExprUtil.StructurallyEqual(lhs, rhs))
                return this.False;

            return UB.BVSGT(lhs, rhs);
        }

        public override Expr BVSGE(Expr lhs, Expr rhs)
        {
            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!lhs.Type.IsBv)
                    throw new ExprTypeCheckException("lhs must be a bitvector");


                // Check the sign of the bitvectors in a two's complement representation
                var threshold = BigInteger.Pow(2, lhsAsLit.asBvConst.Bits - 1);

                bool lhsIsPositiveOrZero = lhsAsLit.asBvConst.Value.ToBigInteger < threshold;
                bool rhsIsPositiveOrZero = rhsAsLit.asBvConst.Value.ToBigInteger < threshold;

                if (lhsIsPositiveOrZero == rhsIsPositiveOrZero)
                {
                    // For this case with twos complement representation
                    //
                    // Notation: (x+ve) means x where x is a positive or zero bitvector under two's complement
                    //  _decimal_rep means the decimal representation of the bitvector treating it as unsigned
                    //
                    //
                    // (x+ve) >= (y+ve) == (x_decimal_rep) >= (y_decimal_rep)
                    // (x-ve) >= (y-ve) == (x_decimal_rep) >= (y_decimal_rep)
                    return ConstantBool(lhsAsLit.asBvConst.Value >= rhsAsLit.asBvConst.Value);
                }
                else if (lhsIsPositiveOrZero && !rhsIsPositiveOrZero)
                {
                    // (x+ve) >= (y-ve) == True
                    return this.True;
                }
                else if (!lhsIsPositiveOrZero && rhsIsPositiveOrZero)
                {
                    // (x-ve) >= (y+ve) == False
                    return this.False;
                }
                else
                {
                    throw new InvalidProgramException("Unreachable!");
                }
            }

            // <expr> >= <expr> ==> true
            //
            // (declare-fun x () (_ BitVec 4))
            // (declare-fun y () (_ BitVec 4))
            // (assert (= x y))
            // (assert (distinct true (bvsge x y)))
            // (check-sat)
            // unsat
            if (ExprUtil.StructurallyEqual(lhs, rhs))
                return this.True;

            return UB.BVSGE(lhs, rhs);
        }

        public override Expr BVULT(Expr lhs, Expr rhs)
        {
            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!lhs.Type.IsBv)
                    throw new ExprTypeCheckException("lhs must be a bitvector");

                return ConstantBool(lhsAsLit.asBvConst.Value < rhsAsLit.asBvConst.Value);
            }

            // <expr> < <expr> ==> false
            //
            // (declare-fun x () (_ BitVec 4))
            // (declare-fun y () (_ BitVec 4))
            // (assert (= x y))
            // (assert (distinct false (bvult x y)))
            // (check-sat)
            // unsat
            if (ExprUtil.StructurallyEqual(lhs, rhs))
                return this.False;

            return UB.BVULT(lhs, rhs);
        }

        public override Expr BVULE(Expr lhs, Expr rhs)
        {
            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!lhs.Type.IsBv)
                    throw new ExprTypeCheckException("lhs must be a bitvector");

                return ConstantBool(lhsAsLit.asBvConst.Value <= rhsAsLit.asBvConst.Value);
            }

            // <expr> <= <expr> ==> true
            //
            // (declare-fun x () (_ BitVec 4))
            // (declare-fun y () (_ BitVec 4))
            // (assert (= x y))
            // (assert (distinct true (bvule x y)))
            // (check-sat)
            // unsat
            if (ExprUtil.StructurallyEqual(lhs, rhs))
                return this.True;

            return UB.BVULE(lhs, rhs);
        }

        public override Expr BVUGT(Expr lhs, Expr rhs)
        {
            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!lhs.Type.IsBv)
                    throw new ExprTypeCheckException("lhs must be a bitvector");

                return ConstantBool(lhsAsLit.asBvConst.Value > rhsAsLit.asBvConst.Value);
            }

            // <expr> > <expr> ==> false
            //
            // (declare-fun x () (_ BitVec 4))
            // (declare-fun y () (_ BitVec 4))
            // (assert (= x y))
            // (assert (distinct false (bvugt x y)))
            // (check-sat)
            // unsat
            if (ExprUtil.StructurallyEqual(lhs, rhs))
                return this.False;

            return UB.BVUGT(lhs, rhs);
        }

        public override Expr BVUGE(Expr lhs, Expr rhs)
        {
            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!lhs.Type.IsBv)
                    throw new ExprTypeCheckException("lhs must be a bitvector");

                return ConstantBool(lhsAsLit.asBvConst.Value >= rhsAsLit.asBvConst.Value);
            }

            // <expr> >= <expr> ==> true
            //
            // (declare-fun x () (_ BitVec 4))
            // (declare-fun y () (_ BitVec 4))
            // (assert (= x y))
            // (assert (distinct true (bvuge x y)))
            // (check-sat)
            // unsat
            if (ExprUtil.StructurallyEqual(lhs, rhs))
                return this.True;

            return UB.BVUGE(lhs, rhs);
        }

        public override Expr BVAND(Expr lhs, Expr rhs)
        {
            // BVAND is commutative so always ensure that if at least one of the operands
            // is constant there will be a constant on the lhs
            if (ExprUtil.AsLiteral(rhs) != null)
            {
                Expr temp = lhs;
                lhs = rhs;
                rhs = temp;
            }

            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!lhs.Type.IsBv)
                    throw new ExprTypeCheckException("lhs must be a bitvector");

                return ConstantBV(lhsAsLit.asBvConst.Value.ToBigInteger & rhsAsLit.asBvConst.Value.ToBigInteger, lhs.Type.BvBits);
            }

            // 0 & <expr> ==> 0
            if (lhsAsLit != null && lhsAsLit.isBvConst && lhsAsLit.asBvConst.Value.IsZero)
            {
                return ConstantBV(0, lhsAsLit.asBvConst.Bits);
            }

            // <all ones> & <expr> ==> <expr>
            if (ExprUtil.IsBVAllOnes(lhs))
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!rhs.Type.IsBv)
                    throw new ExprTypeCheckException("rhs must be a bitvector");

                return rhs;
            }

            // Use associativity and commutivity to rewrite
            // a + (b + c) ==> (a + b) +c  where a is a constant
            // The aim to try to propagate constants up (towards the root)
            var rhsAsBVAND = ExprUtil.AsBVAND(rhs);
            if (rhsAsBVAND != null)
            {
                var rhsBVANDlhs = rhsAsBVAND.Args[0];
                var rhsBVANDrhs = rhsAsBVAND.Args[1];

                var rhsBVANDlhsAsLit = ExprUtil.AsLiteral(rhsBVANDlhs);
                if (lhsAsLit != null && rhsBVANDlhsAsLit != null)
                {
                    //     &
                    //    / \
                    //   1   &
                    //      / \
                    //      2 x
                    // fold to
                    // (1 & 2) & x
                    return BVAND(BVAND(lhsAsLit, rhsBVANDlhsAsLit), rhsBVANDrhs);
                }
                else if (rhsBVANDlhsAsLit != null)
                {
                    //     &
                    //    / \
                    //   x   &
                    //      / \
                    //     1  y
                    // propagate constant up
                    //  1 & (x & y)
                    Debug.Assert(lhsAsLit == null);
                    return BVAND(rhsBVANDlhsAsLit, BVAND(lhs, rhsBVANDrhs));
                }
            }

            // <expr> & <expr> ==> <expr>
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                return lhs;
            }

            return UB.BVAND(lhs, rhs);
        }

        public override Expr BVOR(Expr lhs, Expr rhs)
        {
            // BVOR is commutative so always ensure that if at least one of the operands
            // is constant there will be a constant on the lhs
            if (ExprUtil.AsLiteral(rhs) != null)
            {
                Expr temp = lhs;
                lhs = rhs;
                rhs = temp;
            }

            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!lhs.Type.IsBv)
                    throw new ExprTypeCheckException("lhs must be a bitvector");

                return ConstantBV(lhsAsLit.asBvConst.Value.ToBigInteger | rhsAsLit.asBvConst.Value.ToBigInteger, lhs.Type.BvBits);
            }

            // 0 | <expr> ==> <expr>
            if (lhsAsLit != null && lhsAsLit.isBvConst && lhsAsLit.asBvConst.Value.IsZero)
            {
                return rhs;
            }

            // <all ones> | <expr> ==> <all ones>
            if (ExprUtil.IsBVAllOnes(lhs))
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!rhs.Type.IsBv)
                    throw new ExprTypeCheckException("rhs must be a bitvector");

                return lhs;
            }

            // Use associativity and commutivity to rewrite
            // a | (b | c) ==> (a | b) | c  where a is a constant
            // The aim to try to propagate constants up (towards the root)
            var rhsAsBVOR = ExprUtil.AsBVOR(rhs);
            if (rhsAsBVOR != null)
            {
                var rhsBVORlhs = rhsAsBVOR.Args[0];
                var rhsBVORrhs = rhsAsBVOR.Args[1];

                var rhsBVORlhsAsLit = ExprUtil.AsLiteral(rhsBVORlhs);
                if (lhsAsLit != null && rhsBVORlhsAsLit != null)
                {
                    //     |
                    //    / \
                    //   1   |
                    //      / \
                    //      2 x
                    // fold to
                    // (1 | 2) | x
                    return BVOR(BVOR(lhsAsLit, rhsBVORlhsAsLit), rhsBVORrhs);
                }
                else if (rhsBVORlhsAsLit != null)
                {
                    //     |
                    //    / \
                    //   x   |
                    //      / \
                    //     1  y
                    // propagate constant up
                    //  1 | (x | y)
                    Debug.Assert(lhsAsLit == null);
                    return BVOR(rhsBVORlhsAsLit, BVOR(lhs, rhsBVORrhs));
                }
            }

            // <expr> | <expr> ==> <expr>
            if (ExprUtil.StructurallyEqual(lhs, rhs))
            {
                return lhs;
            }

            return UB.BVOR(lhs, rhs);
        }

        //!
        public override Expr BVXOR(Expr lhs, Expr rhs)
        {
            // BVOR is commutative so always ensure that if at least one of the operands
            // is constant there will be a constant on the lhs
            if (ExprUtil.AsLiteral(rhs) != null)
            {
                Expr temp = lhs;
                lhs = rhs;
                rhs = temp;
            }

            var lhsAsLit = ExprUtil.AsLiteral(lhs);
            var rhsAsLit = ExprUtil.AsLiteral(rhs);
            if (lhsAsLit != null && rhsAsLit != null)
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!lhs.Type.IsBv)
                    throw new ExprTypeCheckException("lhs must be a bitvector");

                return ConstantBV(lhsAsLit.asBvConst.Value.ToBigInteger ^ rhsAsLit.asBvConst.Value.ToBigInteger, lhs.Type.BvBits);
            }

            // 0 ^ <expr> ==> <expr>
            // (declare-fun x () (_ BitVec 4))
            // (declare-fun y () (_ BitVec 4))
            // (assert (distinct y (bvxor (_ bv0 4) y)))
            // (check-sat)
            // unsat
            if (lhsAsLit != null && lhsAsLit.isBvConst && lhsAsLit.asBvConst.Value.IsZero)
            {
                return rhs;
            }

            // <all ones> ^ <expr> ==> (bvnot <expr>)
            // (declare-fun x () (_ BitVec 4))
            // (declare-fun y () (_ BitVec 4))
            // (assert (distinct (bvnot y) (bvxor (_ bv15 4) y)))
            // (check-sat)
            // unsat
            if (ExprUtil.IsBVAllOnes(lhs))
            {
                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!rhs.Type.IsBv)
                    throw new ExprTypeCheckException("rhs must be a bitvector");

                return BVNOT(rhs);
            }

            // Use associativity and commutivity to rewrite
            // a ^ (b ^ c) ==> (a ^ b) ^ c  where a is a constant
            // The aim to try to propagate constants up (towards the root)
            var rhsAsBVXOR = ExprUtil.AsBVXOR(rhs);
            if (rhsAsBVXOR != null)
            {
                var rhsBVXORlhs = rhsAsBVXOR.Args[0];
                var rhsBVXORrhs = rhsAsBVXOR.Args[1];

                var rhsBVXORlhsAsLit = ExprUtil.AsLiteral(rhsBVXORlhs);
                if (lhsAsLit != null && rhsBVXORlhsAsLit != null)
                {
                    //     ^
                    //    / \
                    //   1   ^
                    //      / \
                    //      2 x
                    // fold to
                    // (1 ^ 2) ^ x
                    return BVXOR(BVXOR(lhsAsLit, rhsBVXORlhsAsLit), rhsBVXORrhs);
                }
                else if (rhsBVXORlhsAsLit != null)
                {
                    //     ^
                    //    / \
                    //   x   ^
                    //      / \
                    //     1  y
                    // propagate constant up
                    //  1 ^ (x ^ y)
                    Debug.Assert(lhsAsLit == null);
                    return BVXOR(rhsBVXORlhsAsLit, BVXOR(lhs, rhsBVXORrhs));
                }
            }

            // <expr> ^ <expr> ==> 0
            if (ExprUtil.StructurallyEqual(lhs, rhs) && lhs.Type.IsBv)
            {
                return ConstantBV(0, lhs.Type.BvBits);
            }

            return UB.BVXOR(lhs, rhs);
        }

        public override Expr BVSHL(Expr lhs, Expr rhs)
        {
            var valueToShift = ExprUtil.AsLiteral(lhs);
            var shiftWidth = ExprUtil.AsLiteral(rhs);
            if (shiftWidth != null)
            {
                var bitWidth = ( lhs.Type.BvBits );

                // <expr> << X (where X is a constant greater or equal to bit width)
                //
                // (declare-fun x () (_ BitVec 4))
                // (declare-fun y () (_ BitVec 4))
                // (assert (bvuge y (_ bv4 4)))
                // (assert (distinct (_ bv0 4) (bvshl x y)))
                // (check-sat)
                // unsat
                if (shiftWidth.asBvConst.Value >= BigNum.FromInt(bitWidth))
                {
                    return ConstantBV(0, bitWidth);
                }

                if (valueToShift != null)
                {
                    if (!lhs.Type.Equals(rhs.Type))
                        throw new ExprTypeCheckException("lhs and rhs types must match");

                    if (!rhs.Type.IsBv)
                        throw new ExprTypeCheckException("rhs must be a bitvector");

                    // SMTLIBv2 definition is
                    //
                    //  [[(bvshl s t)]] := nat2bv[m](bv2nat([[s]]) * 2^(bv2nat([[t]])))
                    //
                    //  nat2bv[m], with 0 < m, which takes a non-negative integer
                    //  n and returns the (unique) bitvector b: [0,...,m) -> {0,1}
                    //    such that
                    //
                    //   b(m-1)*2^{m-1} + ... + b(0)*2^0 = n rem 2^m
                    //
                    // NOTE: Even though there is a "rem 2^m" there when the multiplication
                    // multiplies all the bits out of the original value then any division by
                    // 2^m is guaranteed to have zero remainder
                    var maxWidthPlusOne = MaxValuePlusOne(bitWidth);
                    var result = ( valueToShift.asBvConst.Value.ToBigInteger << shiftWidth.asBvConst.Value.ToIntSafe ) % maxWidthPlusOne;
                    Debug.Assert(result < ( BigInteger.Pow(2, bitWidth) - 1 ));
                    return ConstantBV(result, bitWidth);
                }
            }
            else if (valueToShift != null && ExprUtil.IsZero(valueToShift))
            {
                // 0 << <expr> ==> 0
                return ConstantBV(0, valueToShift.Type.BvBits);
            }


            // <expr> << 0 ==> <expr>
            if (ExprUtil.IsZero(shiftWidth))
            {
                return lhs;
            }

            return UB.BVSHL(lhs, rhs);
        }

        public override Expr BVLSHR(Expr lhs, Expr rhs)
        {
            var valueToShift = ExprUtil.AsLiteral(lhs);
            var shiftWidth = ExprUtil.AsLiteral(rhs);
            if (shiftWidth != null)
            {
                var bitWidth = ( lhs.Type.BvBits );

                // <expr> >> X (where X is a constant greater or equal to bit width)
                //
                // (declare-fun x () (_ BitVec 4))
                // (declare-fun y () (_ BitVec 4))
                // (assert (bvuge y (_ bv4 4)))
                // (assert (distinct (_ bv0 4) (bvlshr x y)))
                // (check-sat)
                // unsat
                if (shiftWidth.asBvConst.Value >= BigNum.FromInt(bitWidth))
                {
                    return ConstantBV(0, bitWidth);
                }

                if (valueToShift != null)
                {
                    if (!lhs.Type.Equals(rhs.Type))
                        throw new ExprTypeCheckException("lhs and rhs types must match");

                    if (!rhs.Type.IsBv)
                        throw new ExprTypeCheckException("rhs must be a bitvector");

                    // SMTLIBv2 defintion is
                    //
                    // [[(bvlshr s t)]] := nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))
                    var maxWidthPlusOne = MaxValuePlusOne(bitWidth);
                    var result = ( valueToShift.asBvConst.Value.ToBigInteger >> shiftWidth.asBvConst.Value.ToIntSafe ) % maxWidthPlusOne;
                    Debug.Assert(result < ( BigInteger.Pow(2, bitWidth) - 1 ));
                    return ConstantBV(result, bitWidth);
                }
            }
            else if (valueToShift != null && ExprUtil.IsZero(valueToShift))
            {
                // 0 >> <expr> ==> 0
                return ConstantBV(0, valueToShift.Type.BvBits);
            }


            // <expr> >> 0 ==> <expr>
            if (ExprUtil.IsZero(shiftWidth))
            {
                return lhs;
            }

            return UB.BVLSHR(lhs, rhs);
        }

        public override Expr BVASHR(Expr lhs, Expr rhs)
        {
            var valueToShift = ExprUtil.AsLiteral(lhs);
            var shiftWidth = ExprUtil.AsLiteral(rhs);

            // <expr> >> X != 0 (where X is a constant greater or equal to bit width)
            //
            // (declare-fun x () (_ BitVec 4))
            // (declare-fun y () (_ BitVec 4))
            // (declare-fun z () (_ BitVec 4))
            // (assert (bvuge y (_ bv5 4)))
            // (assert (= z (bvashr x y)))
            // (assert (distinct (_ bv0 4) z)))
            // (check-sat)
            // sat
            //
            // So we can't fold to zero (or to all ones). It depends on the sign of valueToShift


            if (shiftWidth != null && valueToShift != null)
            {
                var bitWidth = ( lhs.Type.BvBits );

                if (!lhs.Type.Equals(rhs.Type))
                    throw new ExprTypeCheckException("lhs and rhs types must match");

                if (!rhs.Type.IsBv)
                    throw new ExprTypeCheckException("rhs must be a bitvector");

                // SMTLIBv2 definition is
                //     (bvashr s t) abbreviates
                //     (ite (= ((_ extract |m-1| |m-1|) s) #b0)
                //     (bvlshr s t)
                //     (bvnot (bvlshr (bvnot s) t)))


                var valueToShiftBI = valueToShift.asBvConst.Value.ToBigInteger;
                Debug.Assert(valueToShiftBI >= 0);
                var shiftWidthBI = shiftWidth.asBvConst.Value.ToBigInteger;
                Debug.Assert(shiftWidthBI >= 0);
                var threshold = BigInteger.Pow(2, bitWidth - 1);
                bool MSBIsZero = valueToShiftBI < threshold;

                BigInteger result = 0;
                if (MSBIsZero)
                {
                    // Fold just like bvlshr
                    result = ( valueToShiftBI >> shiftWidth.asBvConst.Value.ToIntSafe ) % MaxValuePlusOne(bitWidth);
                }
                else
                {
                    // Shift the inverted bit pattern
                    var invertedValueToShift = InvertDecimalReprBVBits(valueToShiftBI, bitWidth);
                    result = invertedValueToShift >> shiftWidth.asBvConst.Value.ToIntSafe;

                    // now invert back
                    result = InvertDecimalReprBVBits(result, bitWidth);
                    result = result % MaxValuePlusOne(bitWidth);
                }
                Debug.Assert(result <= ( BigInteger.Pow(2, bitWidth) - 1 ));
                return ConstantBV(result, bitWidth);

            }

            if (ExprUtil.IsZero(lhs))
            {
                // 0 >> <expr> ==> 0
                //
                // (declare-fun x () (_ BitVec 4))
                // (assert (distinct (_ bv0 4) (bvashr (_ bv0 4) x)))
                // (check-sat)
                // unsat
                return ConstantBV(0, valueToShift.Type.BvBits);
            }


            // <expr> >> 0 ==> <expr>
            //
            // (declare-fun x () (_ BitVec 4))
            // (assert (distinct x (bvashr x (_ bv0 4))))
            // (check-sat)
            // unsat
            if (ExprUtil.IsZero(rhs))
            {
                return lhs;
            }

            return UB.BVASHR(lhs, rhs);
        }

        public override Expr ArithmeticCoercion(Microsoft.Boogie.ArithmeticCoercion.CoercionType coercionType, Expr operand)
        {
            var asLit = ExprUtil.AsLiteral(operand);
            if (asLit != null)
            {
                switch (coercionType)
                {
                    case Microsoft.Boogie.ArithmeticCoercion.CoercionType.ToInt:
                        if (!operand.Type.IsReal)
                            throw new ExprTypeCheckException("To coerce to int operand must be of a real type");

                        // From SMT-LIBv2:
                        //   - to_int as the function that maps each real number r to its integer part,
                        // that is, to the largest integer n that satisfies (<= (to_real n) r)
                        //
                        // Basically that means we need to floor the value towards - infinity
                        var valueReal = asLit.asBigDec;
                        BigInteger floor;
                        BigInteger ceiling;
                        valueReal.FloorCeiling(out floor, out ceiling);
                        // We expect floor to round towards infinity
                        Debug.Assert(floor <= ceiling);

                        return ConstantInt(floor);
                    case Microsoft.Boogie.ArithmeticCoercion.CoercionType.ToReal:
                        if (!operand.Type.IsInt)
                            throw new ExprTypeCheckException("To coerce to int operand must be of a real type");

                        var valueInt = asLit.asBigNum;
                        var bigDec = BigDec.FromBigInt(valueInt.ToBigInteger);
                        return ConstantReal(bigDec);
                    default:
                        throw new NotImplementedException("Coercion type " + coercionType.ToString() + " not supported");
                }
            }

            return UB.ArithmeticCoercion(coercionType, operand);
        }

        // FIXME: This choice is kind of arbitrary and overly pesimistic
        // but this suggests we need a different representation for Maps that allows looking for
        // constant assignment in less than O(n). Walking the entire list of updates in the worst
        // case is now desirable.
        private readonly int MaxMapSelectLookDepth = 5;
        public override Expr MapSelect(Expr map, params Expr[] indices)
        {
            // If this MapSelect is being built on top of map stores
            // see if we can pick out the relevant store
            var asMapStore = ExprUtil.AsMapStore(map);
            if (asMapStore != null)
            {
                if (!map.Type.IsMap)
                {
                    throw new ExprTypeCheckException("map must be of map type");
                }

                if (indices.Length < 1)
                {
                    throw new ArgumentException("Must pass at least one index");
                }

                if (map.Type.AsMap.MapArity != indices.Length)
                {
                    throw new ArgumentException("the number of arguments does not match the map arity");
                }

                int count = 0;
                bool hasConcreteIndicies = true;
                do
                {
                    ++count;

                    var mapStoredTo = asMapStore.Args[0];
                    var mapArity = map.Type.AsMap.MapArity;
                    var mapStoreIndicies = new List<Expr>();
                    for (int index=0; index < mapArity ; ++index)
                    {
                        mapStoreIndicies.Add(asMapStore.Args[index + 1]);
                    }
                    var mapStoreValue = asMapStore.Args[mapArity + 1];

                    // Go over the indicies and see if it matches.
                    // We can only go deeper if all indicies are concrete and no match is found
                    bool indiciesAllMatched = true;
                    for (int index = 0; index < mapArity; ++ index)
                    {
                        var selectIndex = indices[index];

                        if (ExprUtil.AsLiteral(selectIndex) == null || ExprUtil.AsLiteral(mapStoreIndicies[index]) == null)
                            hasConcreteIndicies = false;

                        if (!ExprUtil.StructurallyEqual(selectIndex, mapStoreIndicies[index]))
                        {
                            indiciesAllMatched = false;
                            break;
                        }
                    }

                    if (indiciesAllMatched)
                    {
                        // We are trying to read from this MapStore so we can just return the stored value
                        return mapStoreValue;
                    }

                    if (hasConcreteIndicies)
                    {
                        // Set up variables for doing deeper. We can only look at
                        // MapStores lower down if all the indicies written by the current
                        // MapStore were concrete and the indicies we are trying to read from are also
                        // concrete and they didn't match
                        asMapStore = ExprUtil.AsMapStore(mapStoredTo);

                        if (asMapStore == null)
                            break;
                    }

                } while (count < this.MaxMapSelectLookDepth && hasConcreteIndicies);
            }

            return UB.MapSelect(map, indices);
        }

        public override Expr MapStore(Expr map, Expr value, params Expr[] indices)
        {
            // Look below us, if there is a store and it's
            // to the same indicies that this map store is for
            // then we can optimise this slightly
            // FIXME: We only look one node down but if the indicies are concrete would
            // potentially keep walk past more map stores (provided we only walk past
            // MapStores with concrete indicies) but this would be really inefficient.
            // This suggests we need to rethink how Symbooglix's executor treats maps.
            var asMapStore = ExprUtil.AsMapStore(map);
            if (asMapStore != null)
            {
                if (!map.Type.IsMap)
                {
                    throw new ExprTypeCheckException("map must be of map type");
                }

                if (indices.Length < 1)
                {
                    throw new ArgumentException("Must pass at least one index");
                }

                if (map.Type.AsMap.MapArity != indices.Length)
                {
                    throw new ArgumentException("the number of arguments does not match the map arity");
                }

                var childMapStoreStoresTo = asMapStore.Args[0];
                var childMapStoreValueStored = asMapStore.Args[asMapStore.Args.Count - 1];

                bool indiciesMatch = true;
                for (int index = 0; index < map.Type.AsMap.MapArity; ++index)
                {
                    if (!ExprUtil.StructurallyEqual(asMapStore.Args[index + 1], indices[index]))
                        indiciesMatch = false;
                }

                if (indiciesMatch)
                {
                    if (ExprUtil.StructurallyEqual(value, childMapStoreValueStored))
                    {
                        // the child store writes exactly the same value as the MapStore that we
                        // are trying to create which is redundant so just return the child Map store
                        // i.e. we just reuse the MapStore that already exists
                        return asMapStore;
                    }

                    // Make a new map store but skip the current childMapStore because it is redundant
                    return UB.MapStore(childMapStoreStoresTo, value, indices);

                }
            }

            return UB.MapStore(map, value, indices);
        }


    }
}

