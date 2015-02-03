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

            // x +x => 2*x where x is an identifier
            // FIXME: We should do this for arbitrary Expr but Equality comparisions aren't cheap right now
            if (lhs is IdentifierExpr && rhs is IdentifierExpr)
            {
                if (lhs.Equals(rhs))
                {
                    if (lhs.Type.IsInt)
                    {
                        return this.Mul(this.ConstantInt(2), lhs);
                    }
                    else if (rhs.Type.IsReal)
                    {
                        return this.Mul(this.ConstantReal("2.0"), lhs);
                    }
                }
            }

            // Associativy a + (b + c) ==> (a + b) + c
            // if a and b are constants (that's why we enforce constants on left)
            // then we can fold into a single "+" operation
            // FIXME: Need an easier way of checking operator type
            if (rhs is NAryExpr)
            {
                var rhsNAry = rhs as NAryExpr;
                if (rhsNAry.Fun is BinaryOperator)
                {
                    var fun = rhsNAry.Fun as BinaryOperator;
                    if (fun.Op == BinaryOperator.Opcode.Add)
                    {
                        if (rhsNAry.Args[0] is LiteralExpr)
                        {
                            var rhsAddLeft = rhsNAry.Args[0] as LiteralExpr;

                            if (literalLhs != null)
                            {
                                //     +
                                //    / \
                                //   1   +
                                //      / \
                                //      2 x
                                // fold to
                                // 3 + x
                                if (literalLhs.isBigNum && rhsAddLeft.isBigNum)
                                {
                                    // Int
                                    var result = this.ConstantInt(( literalLhs.asBigNum + rhsAddLeft.asBigNum ).ToBigInteger);
                                    return this.Add(result, rhsNAry.Args[1]);
                                }
                                else if (literalLhs.isBigDec && rhsAddLeft.isBigDec)
                                {
                                    //real
                                    var result = this.ConstantReal(literalLhs.asBigDec + rhsAddLeft.asBigDec);
                                    return this.Add(result, rhsNAry.Args[1]);
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
                                var newSubExprAdd = this.Add(lhs, rhsNAry.Args[1]);
                                return this.Add(rhsAddLeft, newSubExprAdd);
                            }
                        }
                    }
                }
            }

            return UB.Add(lhs, rhs);
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
            // TODO: Move constants to left hand side so we expect constants to always be on the left
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

            // !!<expr> ==> <expr>
            var asNot = ExprUtil.AsNot(e);
            if (asNot != null)
            {
                return asNot.Args[0];
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

            // TODO: There are more cases we can handle here.
            // TODO: 0 - <expr> ==> -<expr>
            // TODO: <expr> - 0 ==> <expr>
            // TODO: <expr> - <constant>  ==> (-<constant>) + <expr>
            // TODO: <expr> - <expr> ==> 0

            // Can't constant fold
            return UB.Sub(lhs, rhs);
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

                var numerator = litLhs.asBigNum;
                var denominator = litRhs.asBigNum;

                // Can't do modulo by zero so check it's safe to compute first
                if (!denominator.IsZero)
                {
                    return this.ConstantInt((numerator % denominator).ToBigInteger);
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

                var numerator = litLhs.asBigNum;
                var denominator = litRhs.asBigNum;

                // Can't do modulo by zero so check it's safe to compute first
                if (!denominator.IsZero)
                {
                    return this.ConstantInt((numerator / denominator).ToBigInteger);
                }
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

            // TODO: Implement propagation of constants upwards like "Add" operator

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

            // TODO: Implement propagation of constants upwards like "Add" operator

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

            // can't constant fold
            return UB.Imp(lhs, rhs);
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
    }
}

