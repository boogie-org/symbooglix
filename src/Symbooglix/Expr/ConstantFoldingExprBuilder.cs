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
                    // (if true then <exprA> else <exprB> ) == <exprA>
                    return thenExpr;
                }
                else if (litCondition.IsFalse)
                {
                    // (if false then <exprA> else <exprB> ) == <exprB>
                    return elseExpr;
                }

            }


            // if <expr> then <expr> else false == <expr>
            // e.g.
            // p1$1:bool := (if BV32_SLT(symbolic_5, 100bv32) then BV32_SLT(symbolic_5, 100bv32) else false)
            if (litElseExpr !=null)
            {
                if (litElseExpr.IsFalse)
                {
                    // More expensive check
                    if (condition.Equals(thenExpr))
                    {
                        return thenExpr;
                    }
                }
            }

            // if !<expr> then <expr> else true == <expr>
            // e.g.
            // p0$1:bool := (if !BV32_SLT(symbolic_5, 100bv32) then BV32_SLT(symbolic_5, 100bv32) else true)
            if (litElseExpr != null)
            {
                if (litElseExpr.IsTrue)
                {
                    // FIXME: We need a better of determining the type of an operator
                    if (condition is NAryExpr)
                    {
                        var conditionNAry = condition as NAryExpr;
                        if (conditionNAry.Fun is UnaryOperator)
                        {
                            var unary = conditionNAry.Fun as UnaryOperator;

                            if (unary.Op == UnaryOperator.Opcode.Not)
                            {
                                // More expensive check
                                if (conditionNAry.Args[0].Equals(thenExpr))
                                {
                                    return thenExpr;
                                }
                            }
                        }
                    }
                }
            }


            //  if <expr> then true else <expr> == <expr>
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

            // we can't constant fold
            return UB.IfThenElse(condition, thenExpr, elseExpr);
        }

        public override Expr NotEq(Expr lhs, Expr rhs)
        {
            // TODO: Move constants to left hand side so we expect constants to always be on the left

            var litLhs = lhs as LiteralExpr;
            var litRhs = rhs as LiteralExpr;
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

            // GPUVerify specific
            // e.g. (in axioms)
            // (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;
            // fold to group_size_y == 1bv32
            if (litRhs != null && lhs is NAryExpr)
            {
                var ift = lhs as NAryExpr;

                if (ift.Fun is IfThenElse)
                {
                    Debug.Assert(ift.Args.Count == 3);
                    var thenExpr = ift.Args[1];
                    var elseExpr = ift.Args[2];

                    if (thenExpr is LiteralExpr && elseExpr is LiteralExpr)
                    {
                        if (elseExpr.Equals(litRhs) && !( thenExpr.Equals(litRhs) ))
                        {
                            return ift.Args[0];
                        }
                        else if (!( elseExpr.Equals(litRhs) ) && thenExpr.Equals(litRhs))
                        {
                            // axiom (if group_size_y == 1bv32 then 0bv1 else 1bv1) != 0bv1;
                            // fold to
                            // ! (group_size_y == 1bv32 )
                            // Can't use Expr.Not() because it may change
                            return this.Not(ift.Args[0]);
                        }
                    }
                }
            }

            return UB.NotEq(lhs, rhs);
        }
    }
}

