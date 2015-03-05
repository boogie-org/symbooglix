using System;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Collections.Generic;
using System.Numerics;
using Microsoft.Basetypes;

namespace Symbooglix
{
    // Clients should use this.
    public class ConstantFoldingTraverser : DFSPostOrderTraverser
    {
        public ConstantFoldingTraverser() : base( new ConstantFoldingVisitor() ) { }
    }

    public class ConstantFoldingVisitor : IExprVisitor
    {
        public Expr VisitLiteralExpr(LiteralExpr e)
        {
            // Can't constant fold a literal
            return e;
        }

        public Expr VisitIdentifierExpr(IdentifierExpr e)
        {
            // This is a symbolic variable so we can't constant fold
            return e;
        }

        public Expr VisitDistinct(NAryExpr e)
        {
            return e;
        }

        public Expr VisitOldExpr(OldExpr e)
        {
            if (e.Expr is LiteralExpr)
            {
                return e.Expr;
            }
            else if (e.Expr is IdentifierExpr)
            {
                var idExpr = e.Expr as IdentifierExpr;
                Debug.Assert(!(idExpr.Decl is Constant), "can't take old of constant");

                if (idExpr.Decl is GlobalVariable)
                    return e;
                else
                {
                    // old(e) ==> e , if e is a non global variable
                    return e.Expr;
                }
            }
            else
                return e;
        }

        public Expr VisitCodeExpr(CodeExpr e)
        {
            throw new NotImplementedException();
        }

        public Expr VisitBvExtractExpr(BvExtractExpr e)
        {
            if (e.Bitvector is LiteralExpr)
            {
                var literal = (LiteralExpr) e.Bitvector;
                Debug.Assert(literal.isBvConst, "Bitvector is not of bitvector type in BvExtractExpr");
                Debug.Assert(e.Start >= 0);
                Debug.Assert(e.End > e.Start);
                var BV = literal.asBvConst;

                // ABitVector[<end>:<start>]
                // This operation selects bits starting at <start> to <end> but not including <end>
               
                // Compute the bit extraction
                BigInteger bitsBeforeStartRemoved = BV.Value.ToBigInteger >> e.Start;
                int numberOfBitsInResult = e.End - e.Start;
                BigInteger bitMask = new BigInteger(( 1 << numberOfBitsInResult ) - 1);
                BigInteger result = bitsBeforeStartRemoved & bitMask; // Mask off bits we don't want
                BigNum resultAsBigNum = BigNum.FromBigInt(result);
                LiteralExpr resultExpr = new LiteralExpr(Token.NoToken, resultAsBigNum, numberOfBitsInResult);
                return resultExpr;
            }
            else
                return e;
        }

        public Expr VisitBvConcatExpr(BvConcatExpr e)
        {
            if (e.E0 is LiteralExpr && e.E1 is LiteralExpr)
            {
                var MSB = e.E0 as LiteralExpr;
                var LSB = e.E1 as LiteralExpr;
                Debug.Assert(MSB.isBvConst, "MSB is not a BvConst");
                Debug.Assert(LSB.isBvConst, "LSB is not a BvConst");
                Debug.WriteLine("Constant folding BvConcatExpr");

                var MSBBV = MSB.asBvConst;
                var LSBBV = LSB.asBvConst;

                // Compute concatentation
                // Note BigInteger is immutable
                BigInteger MSBShifted = MSBBV.Value.ToBigInteger << LSBBV.Bits;
                BigInteger resultAsBigInt = MSBShifted + LSBBV.Value.ToBigInteger;
                BigNum resultAsBigNum = BigNum.FromBigInt(resultAsBigInt);
                LiteralExpr result = new LiteralExpr(Token.NoToken, resultAsBigNum, MSBBV.Bits + LSBBV.Bits);
                return result;
            }
            else
                return e;
        }

        public Expr VisitForallExpr(ForallExpr e)
        {
            // ∀ x : true  <==> true
            // ∀ x : false  <==> false
            if (e.Body is LiteralExpr)
            {
                var literal = (LiteralExpr) e.Body;
                Debug.Assert(literal.isBool);
                return literal;
            }
            else
                return e;
        }

        public Expr VisitExistExpr(ExistsExpr e)
        {
            // ∃ x : true  <==> true
            // ∃ x : false  <==> false
            if (e.Body is LiteralExpr)
            {
                var literal = (LiteralExpr) e.Body;
                Debug.Assert(literal.isBool);
                return literal;
            }
            else
                return e;
        }

        public Expr VisitLambdaExpr(LambdaExpr e)
        {
            // We can't constant fold these.
            return e;
        }

        public Expr VisitNot(NAryExpr e)
        {
            if (e.Args[0] is LiteralExpr)
            {
                var literal = (LiteralExpr) e.Args[0];
                if (literal.IsTrue)
                    return Expr.False;
                else if (literal.IsFalse)
                    return Expr.True;
                else
                    throw new Exception("Invalid operand to Not");
            }
            else
                return e;
        }

        public Expr VisitNeg(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 1);
            if (e.Args[0] is LiteralExpr)
            {
                var literal = (LiteralExpr) e.Args[0];

                if (literal.isBigNum)
                {
                    // Int
                    var newValue = BigNum.FromBigInt(literal.asBigNum.ToBigInteger * -1);
                    return new LiteralExpr(Token.NoToken, newValue);
                }
                else if (literal.isBigDec)
                {
                    // Real
                    return new LiteralExpr(Token.NoToken, literal.asBigDec.Negate);
                }
                else
                {
                    throw new NotSupportedException();
                }
            }
            else
                return e;
        }

        public Expr VisitAdd(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var LHS = e.Args[0] as LiteralExpr;
                var RHS = e.Args[1] as LiteralExpr;
                Debug.Assert(LHS.Type == RHS.Type, "Mismatching types");
                if (LHS.isBigNum && RHS.isBigNum)
                {
                    // Int
                    return new LiteralExpr(Token.NoToken, LHS.asBigNum + RHS.asBigNum);
                }
                else if (LHS.isBigDec && RHS.isBigDec)
                {
                    // Real
                    return new LiteralExpr(Token.NoToken, LHS.asBigDec + RHS.asBigDec);
                }
                else
                    throw new NotSupportedException("Unsupported types in + constant fold");
            }
            else
                return e;
        }

        public Expr VisitSub(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var LHS = e.Args[0] as LiteralExpr;
                var RHS = e.Args[1] as LiteralExpr;
                Debug.Assert(LHS.Type == RHS.Type, "Mismatching types");
                if (LHS.isBigNum && RHS.isBigNum)
                {
                    // Int
                    return new LiteralExpr(Token.NoToken, LHS.asBigNum - RHS.asBigNum);
                }
                else if (LHS.isBigDec && RHS.isBigDec)
                {
                    // Real
                    return new LiteralExpr(Token.NoToken, LHS.asBigDec - RHS.asBigDec);
                }
                else
                    throw new NotSupportedException("Unsupported types in - constant fold");
            }
            else
                return e;
        }

        public Expr VisitMul(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var LHS = e.Args[0] as LiteralExpr;
                var RHS = e.Args[1] as LiteralExpr;
                Debug.Assert(LHS.Type == RHS.Type, "Mismatching types");
                if (LHS.isBigNum && RHS.isBigNum)
                {
                    // Int
                    return new LiteralExpr(Token.NoToken, LHS.asBigNum * RHS.asBigNum);
                }
                else if (LHS.isBigDec && RHS.isBigDec)
                {
                    // Real
                    return new LiteralExpr(Token.NoToken, LHS.asBigDec * RHS.asBigDec);
                }
                else
                    throw new NotSupportedException("Unsupported types in - constant fold");
            }
            else
                return e;
        }

        public Expr VisitDiv(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                Debug.Assert(( e.Args[0] as LiteralExpr ).isBigNum, "numerator is wrong type");
                Debug.Assert(( e.Args[1] as LiteralExpr ).isBigNum, "denominator is wrong type");
                var numerator = (e.Args[0] as LiteralExpr).asBigNum;
                var denominator = (e.Args[1] as LiteralExpr).asBigNum;

                if (denominator.IsZero)
                {
                    // Can't do division by zero so leave the expression as it is
                    return e;
                }

                return new LiteralExpr(Token.NoToken, numerator / denominator);
            }
            else
                return e;
        }

        public Expr VisitMod(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                Debug.Assert(( e.Args[0] as LiteralExpr ).isBigNum, "numerator is wrong type");
                Debug.Assert(( e.Args[1] as LiteralExpr ).isBigNum, "denominator is wrong type");
                var numerator = (e.Args[0] as LiteralExpr).asBigNum;
                var denominator = (e.Args[1] as LiteralExpr).asBigNum;

                if (denominator.IsZero)
                {
                    // Can't do modulo by zero so leave the expression as it is
                    return e;
                }

                return new LiteralExpr(Token.NoToken, numerator % denominator);
            }
            else
                return e;
        }

        public Expr VisitRem(NAryExpr e)
        {
            // This is a Z3 extension. Don't try constant folding for now
            return e;
        }

        public Expr VisitRealDiv(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr VisitPow(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Expr VisitEq(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.Type == arg1.Type);

                if (arg0.isBvConst)
                {
                    if (arg0.asBvConst.Equals(arg1.asBvConst)) // make sure we use Equals and not ``==`` which does reference equality
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else if (arg0.isBool)
                {
                    if (arg0.asBool == arg1.asBool)
                        return Expr.True;
                    else
                        return Expr.False;

                }
                else if (arg0.isBigNum)
                {
                    if (arg0.asBigNum.Equals(arg1.asBigNum))
                        return Expr.True;
                    else
                        return Expr.False;

                }
                else if (arg0.isBigDec)
                {
                    if (arg0.asBigDec.Equals(arg1.asBigDec))
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else
                    throw new NotImplementedException(); // Unreachable?

            }

            // Check for structural equivalence
            if (e.Args[0].Equals(e.Args[1]))
                return Expr.True;

            // Can't constant fold
            return e;
        }

        public Expr VisitNeq(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.Type == arg1.Type);

                if (arg0.isBvConst)
                {
                    if (arg0.asBvConst.Equals(arg1.asBvConst)) // make sure we use Equals and not ``==`` which does reference equality
                        return Expr.False;
                    else
                        return Expr.True;
                }
                else if (arg0.isBool)
                {
                    if (arg0.asBool == arg1.asBool)
                        return Expr.False;
                    else
                        return Expr.True;

                }
                else if (arg0.isBigNum)
                {
                    if (arg0.asBigNum.Equals(arg1.asBigNum))
                        return Expr.False;
                    else
                        return Expr.True;

                }
                else if (arg0.isBigDec)
                {
                    if (arg0.asBigDec.Equals(arg1.asBigDec))
                        return Expr.False;
                    else
                        return Expr.True;
                }
                else
                    throw new NotImplementedException(); // Unreachable?
            }

            // GPUVerify specific
            // e.g. (in axioms)
            // (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;
            // fold to group_size_y == 1bv32
            if (e.Args[1] is LiteralExpr && e.Args[0] is NAryExpr)
            {
                var ift = e.Args[0] as NAryExpr;
                var constant = e.Args[1] as LiteralExpr;

                if (ift.Fun is IfThenElse)
                {
                    Debug.Assert(ift.Args.Count == 3);
                    var thenExpr = ift.Args[1];
                    var elseExpr = ift.Args[2];

                    if (thenExpr is LiteralExpr && elseExpr is LiteralExpr)
                    {
                        if (elseExpr.Equals(constant) && !( thenExpr.Equals(constant) ))
                        {
                            return ift.Args[0];
                        }
                        else if (!( elseExpr.Equals(constant) ) && thenExpr.Equals(constant))
                        {
                            // axiom (if group_size_y == 1bv32 then 0bv1 else 1bv1) != 0bv1;
                            // fold to
                            // ! (group_size_y == 1bv32 )
                            // Can't use Expr.Not() because it may change
                            return new NAryExpr(Token.NoToken, new UnaryOperator(Token.NoToken, UnaryOperator.Opcode.Not), new List<Expr>() { ift.Args[0] });
                        }
                    }
                }
            }

            // Can't constant fold
            return e;
        }

        public Expr VisitGt(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var LHS = e.Args[0] as LiteralExpr;
                var RHS = e.Args[1] as LiteralExpr;
                Debug.Assert(LHS.Type == RHS.Type, "Mismatching types");
                if (LHS.isBigNum && RHS.isBigNum)
                {
                    // Int
                    if (LHS.asBigNum > RHS.asBigNum)
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else if (LHS.isBigDec && RHS.isBigDec)
                {
                    // Real
                    if (LHS.asBigDec > RHS.asBigDec)
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else
                    throw new NotSupportedException("Unsupported types in >  constant fold");
            }
            else
                return e;
        }

        public Expr VisitGe(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var LHS = e.Args[0] as LiteralExpr;
                var RHS = e.Args[1] as LiteralExpr;
                Debug.Assert(LHS.Type == RHS.Type, "Mismatching types");
                if (LHS.isBigNum && RHS.isBigNum)
                {
                    // Int
                    if (LHS.asBigNum >= RHS.asBigNum)
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else if (LHS.isBigDec && RHS.isBigDec)
                {
                    // Real
                    if (LHS.asBigDec >= RHS.asBigDec)
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else
                    throw new NotSupportedException("Unsupported types in >=  constant fold");
            }
            else
                return e;
        }

        public Expr VisitLt(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var LHS = e.Args[0] as LiteralExpr;
                var RHS = e.Args[1] as LiteralExpr;
                Debug.Assert(LHS.Type == RHS.Type, "Mismatching types");
                if (LHS.isBigNum && RHS.isBigNum)
                {
                    // Int
                    if (LHS.asBigNum < RHS.asBigNum)
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else if (LHS.isBigDec && RHS.isBigDec)
                {
                    // Real
                    if (LHS.asBigDec < RHS.asBigDec)
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else
                    throw new NotSupportedException("Unsupported types in <  constant fold");
            }
            else
                return e;
        }

        public Expr VisitLe(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var LHS = e.Args[0] as LiteralExpr;
                var RHS = e.Args[1] as LiteralExpr;
                Debug.Assert(LHS.Type == RHS.Type, "Mismatching types");
                if (LHS.isBigNum && RHS.isBigNum)
                {
                    // Int
                    if (LHS.asBigNum <= RHS.asBigNum)
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else if (LHS.isBigDec && RHS.isBigDec)
                {
                    // Real
                    if (LHS.asBigDec <= RHS.asBigDec)
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else
                    throw new NotSupportedException("Unsupported types in <=  constant fold");
            }
            else
                return e;
        }

        public Expr VisitAnd(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);

            // false AND <expr> == false
            // <expr> AND false == false
            for (int index = 0; index <= 1; ++index)
            {
                if (e.Args[index] is LiteralExpr)
                {
                    var literal = e.Args[index] as LiteralExpr;
                    Debug.Assert(literal.isBool, "literal is not bool");

                    if (literal.IsFalse)
                        return Expr.False;
                }
            }

            // true and true == true
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBool, "arg0 is not bool");
                Debug.Assert(arg1.isBool, "arg1 is not bool");

                if (arg0.IsTrue && arg1.IsTrue)
                    return Expr.True;
            }

            // true and <expr> == <expr>
            for (int index = 0; index <=1; ++index)
            {
                if (e.Args[index] is LiteralExpr)
                {
                    var literal = e.Args[index] as LiteralExpr;

                    if (literal.IsTrue)
                    {
                        return e.Args[( index + 1 ) % 2];
                    }
                }
            }

            return e;
        }

        public Expr VisitOr(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);

            // true OR <expr> == true
            // <expr> OR true == true
            for (int index = 0; index <= 1; ++index)
            {
                if (e.Args[index] is LiteralExpr)
                {
                    LiteralExpr literal = e.Args[index] as LiteralExpr;
                    Debug.Assert(literal.isBool);

                    if (literal.IsTrue)
                        return Expr.True;
                }
            }

            // false OR false == false
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.IsFalse && arg1.IsFalse);
                return Expr.False;
            }

            // false OR <expr> == <expr>
            for (int index = 0; index <= 1; ++index)
            {
                if (e.Args[index] is LiteralExpr)
                {
                    var literal = e.Args[index] as LiteralExpr;

                    if (literal.IsFalse)
                    {
                        return e.Args[( index + 1 ) % 2];
                    }
                }
            }

            // Can't constant fold
            return e;
        }

        public Expr VisitImp(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);

            if (e.Args[0] is LiteralExpr)
            {
                var literal = e.Args[0] as LiteralExpr;
                Debug.Assert(literal.isBool);

                // true -> <expr> == <expr>
                if (literal.IsTrue)
                    return e.Args[1];
                // false -> <expr> == true
                else if (literal.IsFalse)
                    return Expr.True;
            }

            // can't constant fold
            return e;
        }

        public Expr VisitIff(NAryExpr e)
        {

            Debug.Assert(e.Args.Count == 2);

            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBool);
                Debug.Assert(arg1.isBool);


                if (arg0.asBool == arg1.asBool)
                {
                    // (true <==> true) == true
                    // (false <==> false) == true
                    return Expr.True;
                }
                else
                {
                    // (true <==> false) == false
                    // (false <==> true) == false
                    return Expr.False;
                }
            }

            // Handle if only one of the args is constant
            for (int index = 0; index <= 1; ++index)
            {
                if (e.Args[index] is LiteralExpr)
                {
                    var literal = e.Args[index] as LiteralExpr;
                    Debug.Assert(literal.isBool);
                    int otherIndex = (index == 0) ? 1 : 0;

                    if (literal.IsTrue)
                    {
                        // ( true <==> <expr> ) == <expr>
                        // ( <expr> <==> true ) == <expr>
                        return e.Args[otherIndex];
                    }
                    else
                    {
                        Debug.Assert(literal.IsFalse);
                        // (false <==> <expr>) == not <expr>
                        // (<expr> <==> false) == not <expr>
                        return Expr.Not(e.Args[otherIndex]);
                    }
                }
            }

            // otherwise we can't constant fold
            return e;
        }

        public Expr VisitSubType(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Expr VisitMapStore(NAryExpr e)
        {
            // Can't do any constant folding without access execution state
            return e;
        }

        public Expr VisitMapSelect(NAryExpr e)
        {
            // Can't do any constant folding without access execution state
            return e;
        }

        public Expr VisitIfThenElse(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 3);
            if (e.Args[0] is LiteralExpr)
            {
                var literal = e.Args[0] as LiteralExpr;
                Debug.Assert(literal.isBool);

                if (literal.IsTrue)
                {
                    // (if true then <exprA> else <exprB> ) == <exprA>
                    return e.Args[1];
                }
                else
                {
                    Debug.Assert(literal.IsFalse);
                    // (if false then <exprA> else <exprB> ) == <exprA>
                    return e.Args[2];
                }
            }

            // if <expr> then <expr> else false == <expr>
            // e.g.
            // p1$1:bool := (if BV32_SLT(symbolic_5, 100bv32) then BV32_SLT(symbolic_5, 100bv32) else false)
            if (e.Args[2] is LiteralExpr)
            {
                var elseExpr = e.Args[2] as LiteralExpr;

                if (elseExpr.IsFalse)
                {
                    // More expensive check
                    if (e.Args[0].Equals(e.Args[1]))
                    {
                        return e.Args[0];
                    }
                }
            }

            // if !<expr> then <expr> else true == <expr>
            // e.g.
            // p0$1:bool := (if !BV32_SLT(symbolic_5, 100bv32) then BV32_SLT(symbolic_5, 100bv32) else true)
            if (e.Args[2] is LiteralExpr)
            {
                var elseExpr = e.Args[2] as LiteralExpr;

                if (elseExpr.IsTrue)
                {
                    if (e.Args[0] is NAryExpr)
                    {
                        var conditionNAry = e.Args[0] as NAryExpr;
                        if (conditionNAry.Fun is UnaryOperator)
                        {
                            var unary = conditionNAry.Fun as UnaryOperator;

                            if (unary.Op == UnaryOperator.Opcode.Not)
                            {
                                // More expensive check
                                if (conditionNAry.Args[0].Equals(e.Args[1]))
                                {
                                    return e.Args[1];
                                }
                            }
                        }
                    }
                }
            }


            //  if <expr> then true else <expr> == <expr>
            // e.g. (if BV32_SLT(symbolic_4, symbolic_20) then true else BV32_SLT(symbolic_4, symbolic_20))
            if (e.Args[1] is LiteralExpr)
            {
                var thenExpr = e.Args[1] as LiteralExpr;
                if (thenExpr.IsTrue)
                {
                    var elseExpr = e.Args[2];
                    if (e.Args[0].Equals(elseExpr))
                    {
                        return e.Args[0];
                    }
                }
            }

            // we can't constant fold
            return e;
        }

        public Expr VisitFunctionCall(NAryExpr e)
        {
            // The executor should (at some point)
            // make sure that Functions
            // that can be inlined already have been so
            // we shouldn't need to do anything.
            return e;
        }

        public Expr VisitTypeCoercion(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 1);
            var typeCoercion = e.Fun as TypeCoercion;
            if (!typeCoercion.Type.Equals(e.Args[0].Type))
                throw new NotSupportedException("Non trivial type coercion used");

            // Remove the trivial TypeCoercion it's not interesting.
            return e.Args[0];
        }

        public Expr VisitArithmeticCoercion(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 1);
            Debug.Assert(e.Fun is ArithmeticCoercion);
            if (e.Args[0] is LiteralExpr)
            {
                var literal = e.Args[0] as LiteralExpr;
                var arithmeticCoercion = e.Fun as ArithmeticCoercion;

                switch (arithmeticCoercion.Coercion)
                {
                    case ArithmeticCoercion.CoercionType.ToInt:
                        Debug.Assert(literal.isBigDec);

                        // Flooring conversion
                        var bigDec = literal.asBigDec;
                        BigInteger flooredValue;
                        BigInteger ceilingValue; // Not used
                        bigDec.FloorCeiling(out flooredValue, out ceilingValue);
                        return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(flooredValue));
                    case ArithmeticCoercion.CoercionType.ToReal:
                        Debug.Assert(literal.isBigNum);
                        var integer = literal.asBigNum;
                        return new LiteralExpr(Token.NoToken, BigDec.FromBigInt(integer.ToBigInteger));
                    default:
                        throw new NotSupportedException("Arithmetic coercion type " + arithmeticCoercion.Coercion + " not supported");
                }
            }

            return e;
        }

        public Expr Visit_bvadd(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                Debug.Assert(arg1.isBvConst);
                Debug.Assert(arg0.asBvConst.Bits == arg1.asBvConst.Bits);

                // Compute bvand
                var MaxValuePlusOne = (new BigInteger(1)) << arg0.asBvConst.Bits ; // 2^( number of bits)
                var arg0BI = arg0.asBvConst.Value.ToBigInteger;
                var arg1BI = arg1.asBvConst.Value.ToBigInteger;
                var result = ( arg0BI + arg1BI ) % MaxValuePlusOne; // Wrapping overflow
                LiteralExpr literal = new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), arg0.asBvConst.Bits);
                return literal;
            }
            else
                return e;
        }

        public Expr Visit_bvsub(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                Debug.Assert(arg1.isBvConst);
                Debug.Assert(arg0.asBvConst.Bits == arg1.asBvConst.Bits);

                // compute bvsub
                // (bvsub s t) abbreviates (bvadd s (bvneg t))
                // note:  [[(bvneg s)]] := nat2bv[m](2^m - bv2nat([[s]]))
                var MaxValuePlusOne = (new BigInteger(1)) << arg0.asBvConst.Bits ; // 2^( number of bits)
                var arg0BI = arg0.asBvConst.Value.ToBigInteger;
                var arg1BI = arg1.asBvConst.Value.ToBigInteger;
                var arg1Negated = MaxValuePlusOne - arg1BI;
                var result = ( arg0BI + arg1Negated ) % MaxValuePlusOne;
                LiteralExpr literal = new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), arg0.asBvConst.Bits);
                return literal;
            }
            else
                return e;
        }

        public Expr Visit_bvmul(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                Debug.Assert(arg1.isBvConst);
                Debug.Assert(arg0.asBvConst.Bits == arg1.asBvConst.Bits);
                // [[(bvmul s t)]] := nat2bv[m](bv2nat([[s]]) * bv2nat([[t]]))

                var MaxValuePlusOne = (new BigInteger(1)) << arg0.asBvConst.Bits ; // 2^( number of bits)

                // % isn't like mod for negative numbers, so using it would be incorrect in this case.
                Debug.Assert(!arg0.asBvConst.Value.IsNegative);
                Debug.Assert(!arg1.asBvConst.Value.IsNegative);
                var result = ( arg0.asBvConst.Value.ToBigInteger * arg1.asBvConst.Value.ToBigInteger ) % MaxValuePlusOne;
                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), arg0.asBvConst.Bits);
            }
            else
                return e;
        }

        public Expr Visit_bvudiv(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                Debug.Assert(arg1.isBvConst);
                Debug.Assert(arg0.asBvConst.Bits == arg1.asBvConst.Bits);

                if (arg1.asBvConst.Value.IsZero)
                {
                    // Can't divide by zero, don't fold
                    return e;
                }

                //    [[(bvudiv s t)]] := if bv2nat([[t]]) != 0 then
                //                           nat2bv[m](bv2nat([[s]]) div bv2nat([[t]]))
                //
                //  Division by zero is not defined by the standard. Just let an exception be
                // thrown for now.
                var MaxValuePlusOne = (new BigInteger(1)) << arg0.asBvConst.Bits ; // 2^( number of bits)
                Debug.Assert(!arg0.asBvConst.Value.IsNegative);
                Debug.Assert(!arg1.asBvConst.Value.IsNegative);
                var result = ( arg0.asBvConst.Value.ToBigInteger / arg1.asBvConst.Value.ToBigInteger ) % MaxValuePlusOne;
                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), arg0.asBvConst.Bits);
            }
            else
                return e;
        }

        public Expr Visit_bvurem(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                // [[(bvurem s t)]] := if bv2nat([[t]]) != 0 then
                //                     nat2bv[m](bv2nat([[s]]) rem bv2nat([[t]]))
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                Debug.Assert(arg1.isBvConst);
                Debug.Assert(arg0.asBvConst.Bits == arg1.asBvConst.Bits);

                if (arg1.asBvConst.Value.IsZero)
                {
                    // Can't divide by zero, don't fold
                    return e;
                }

                var MaxValuePlusOne = (new BigInteger(1)) << arg0.asBvConst.Bits ; // 2^( number of bits)
                Debug.Assert(!arg0.asBvConst.Value.IsNegative);
                Debug.Assert(!arg1.asBvConst.Value.IsNegative);

                var result = ( arg0.asBvConst.Value.ToBigInteger % arg1.asBvConst.Value.ToBigInteger ) % MaxValuePlusOne;
                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), arg0.asBvConst.Bits);

            }
            else
                return e;
        }

        private BigInteger BvNegOnNaturalNumber(BigInteger value, int bitwidth)
        {
            var MaxValuePlusOne = (new BigInteger(1)) << bitwidth ; // 2^( number of bits)
            return ( MaxValuePlusOne - value ) % MaxValuePlusOne;
        }

        public Expr Visit_bvsdiv(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var numerator = e.Args[0] as LiteralExpr;
                var denominator = e.Args[1] as LiteralExpr;
                Debug.Assert(numerator.isBvConst);
                Debug.Assert(denominator.isBvConst);
                Debug.Assert(numerator .asBvConst.Bits == denominator.asBvConst.Bits);

                if (denominator.asBvConst.Value.IsZero)
                {
                    // Can't divide by zero, don't fold
                    return e;
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
                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), numerator.asBvConst.Bits);
            }
            else
                return e;
        }

        public Expr Visit_bvsrem(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var numerator = e.Args[0] as LiteralExpr;
                var denominator = e.Args[1] as LiteralExpr;
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
                    return e;
                }

                // Check the sign of the bitvector in a two's complement representation
                int bitwidth = numerator.asBvConst.Bits;
                var threshold = BigInteger.Pow(2, bitwidth - 1);
                var MaxValuePlusOne = (new BigInteger(1)) << bitwidth ; // 2^( number of bits)

                bool numeratorIsPositiveOrZero = numerator.asBvConst.Value.ToBigInteger < threshold;
                bool denominatorIsPositiveOrZero = denominator.asBvConst.Value.ToBigInteger < threshold;

                BigInteger result=0;

                if (numeratorIsPositiveOrZero && denominatorIsPositiveOrZero)
                {
                    result = (numerator.asBvConst.Value.ToBigInteger %
                              denominator.asBvConst.Value.ToBigInteger) % MaxValuePlusOne;
                }
                else if (!numeratorIsPositiveOrZero && denominatorIsPositiveOrZero)
                {
                    result = BvNegOnNaturalNumber(
                                                  BvNegOnNaturalNumber(numerator.asBvConst.Value.ToBigInteger, bitwidth) %
                                                  denominator.asBvConst.Value.ToBigInteger,
                                                  bitwidth
                                                 ) % MaxValuePlusOne;
                }
                else if (numeratorIsPositiveOrZero && !denominatorIsPositiveOrZero)
                {
                    result = (
                              numerator.asBvConst.Value.ToBigInteger %
                              BvNegOnNaturalNumber(denominator.asBvConst.Value.ToBigInteger, bitwidth )
                             ) % MaxValuePlusOne;
                }
                else
                {
                    Debug.Assert(!numeratorIsPositiveOrZero && !denominatorIsPositiveOrZero);
                    result = ( BvNegOnNaturalNumber(numerator.asBvConst.Value.ToBigInteger, bitwidth) %
                              BvNegOnNaturalNumber(denominator.asBvConst.Value.ToBigInteger, bitwidth) ) % MaxValuePlusOne;
                }

                Debug.Assert(result >= 0);
                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), numerator.asBvConst.Bits);
            }
            else
                return e;
        }

        public Expr Visit_bvsmod(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                Debug.Assert(( e.Args[0] as LiteralExpr ).isBvConst);
                Debug.Assert(( e.Args[1] as LiteralExpr ).isBvConst);
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

                var numerator = ( e.Args[0] as LiteralExpr ).asBvConst;
                var denominator = ( e.Args[1] as LiteralExpr ).asBvConst;
                int bitWidth = numerator.Bits;
                Debug.Assert(numerator.Bits == denominator.Bits);
                Debug.Assert(!numerator.Value.IsNegative);
                Debug.Assert(!denominator.Value.IsNegative);

                if (denominator.Value.IsZero)
                {
                    // Can't do bvsmod by zero so don't fold
                    return e;
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

                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), bitWidth);
            }
            else
                return e;
        }

        public Expr Visit_sign_extend(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 1);
            if (e.Args[0] is LiteralExpr)
            {
                var literal = e.Args[0] as LiteralExpr;
                Debug.Assert(literal.isBvConst);

                // Get new size
                int newWidth = e.Type.BvBits;
                Debug.Assert(newWidth >= literal.asBvConst.Bits);


                if (newWidth == literal.asBvConst.Bits)
                {
                    // Not doing any extending so just return the literal
                    return literal;
                }

                // Check the sign of the bitvector in a two's complement representation
                var threshold = BigInteger.Pow(2, literal.asBvConst.Bits - 1);

                if (literal.asBvConst.Value.ToBigInteger < threshold)
                {
                    // The bitvector is a positive bitvector under two's complement interpretation
                    // So sign extend does not change internal representation
                    var newLiteral = new LiteralExpr(Token.NoToken, literal.asBvConst.Value, newWidth);
                    return newLiteral;
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
                    var maxOldPlusOne = BigInteger.Pow(2, literal.asBvConst.Bits);
                    var result = (maxNewPlusOne - maxOldPlusOne) + literal.asBvConst.Value.ToBigInteger;
                    var newLiteral = new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), newWidth);
                    return newLiteral;
                }
            }
            else
                return e;
        }

        public Expr Visit_zero_extend(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 1);
            Debug.Assert(e.Type.IsBv);
            if (e.Args[0] is LiteralExpr)
            {
                var literal = e.Args[0] as LiteralExpr;
                Debug.Assert(literal.isBvConst);

                // Get new size
                int newWidth = e.Type.BvBits;
                Debug.Assert(newWidth >= literal.asBvConst.Bits);

                if (newWidth == literal.asBvConst.Bits)
                {
                    // Not doing any extending so just return the literal
                    return literal;
                }

                // Zero extend is very simple, we just make a wider bitvector with the same natural number representation
                var newLiteral = new LiteralExpr(Token.NoToken, literal.asBvConst.Value, newWidth);
                return newLiteral;
            }
            else
                return e;
        }

        public Expr Visit_bvneg(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 1);
            if (e.Args[0] is LiteralExpr)
            {
                var literal = e.Args[0] as LiteralExpr;
                Debug.Assert(literal.isBvConst);
                int bitwidth = literal.asBvConst.Bits;
                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(BvNegOnNaturalNumber(literal.asBvConst.Value.ToBigInteger,bitwidth)), bitwidth);
            }
            else
                return e;
        }

        public Expr Visit_bvand(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                Debug.Assert(arg1.isBvConst);
                var bitWidth = ( arg0.asBvConst.Bits );
                return new LiteralExpr(Token.NoToken,
                                       BigNum.FromBigInt(arg0.asBvConst.Value.ToBigInteger & arg1.asBvConst.Value.ToBigInteger),
                                       bitWidth);
            }
            else
                return e;
        }

        public Expr Visit_bvor(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                Debug.Assert(arg1.isBvConst);
                var bitWidth = ( arg0.asBvConst.Bits );
                return new LiteralExpr(Token.NoToken,
                                       BigNum.FromBigInt(arg0.asBvConst.Value.ToBigInteger | arg1.asBvConst.Value.ToBigInteger),
                                       bitWidth);
            }
            else
                return e;
        }

        public Expr Visit_bvnot(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 1);
            if (e.Args[0] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                var bitWidth = arg0.asBvConst.Bits;
                var result = InvertDecimalReprBVBits(arg0.asBvConst.Value.ToBigInteger, bitWidth);
                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), bitWidth);
            }
            else
                return e;
        }

        private BigInteger InvertDecimalReprBVBits(BigInteger decimalRepr, int bitWidth)
        {
            Debug.Assert(bitWidth > 0);
            var bitMask = BigInteger.Pow(2, bitWidth) -1; // Decimal representation of all ones
            var result = decimalRepr ^ bitMask; // Using Xor with all ones will invert all the bits
            return result;
        }

        public Expr Visit_bvxor(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                Debug.Assert(arg1.isBvConst);
                var bitWidth = ( arg0.asBvConst.Bits );
                return new LiteralExpr(Token.NoToken,
                                       BigNum.FromBigInt(arg0.asBvConst.Value.ToBigInteger ^ arg1.asBvConst.Value.ToBigInteger),
                                       bitWidth);
            }
            else
                return e;
        }

        public Expr Visit_bvshl(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var valueToShift = e.Args[0] as LiteralExpr;
                var shiftWidth = e.Args[1] as LiteralExpr;
                Debug.Assert(valueToShift.isBvConst);
                Debug.Assert(shiftWidth.isBvConst);
                Debug.Assert(valueToShift.asBvConst.Bits == shiftWidth.asBvConst.Bits);
                var bitWidth = ( valueToShift.asBvConst.Bits );

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
                if (shiftWidth.asBvConst.Value >= BigNum.FromInt(bitWidth))
                {
                    return new LiteralExpr(Token.NoToken, BigNum.FromInt(0), bitWidth);
                }
                else
                {
                    var result = ( valueToShift.asBvConst.Value.ToBigInteger << shiftWidth.asBvConst.Value.ToIntSafe );
                    result = BigInteger.Remainder(result, BigInteger.Pow(2, bitWidth)); 
                    Debug.Assert(result < ( BigInteger.Pow(2, bitWidth) - 1 ));
                    return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), bitWidth);
                }
            }
            else
                return e;
        }

        public Expr Visit_bvlshr(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var valueToShift = e.Args[0] as LiteralExpr;
                var shiftWidth = e.Args[1] as LiteralExpr;
                Debug.Assert(valueToShift.isBvConst);
                Debug.Assert(shiftWidth.isBvConst);
                Debug.Assert(valueToShift.asBvConst.Bits == shiftWidth.asBvConst.Bits);
                var bitWidth = ( valueToShift.asBvConst.Bits );
                // SMTLIBv2 defintion is
                //
                // [[(bvlshr s t)]] := nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))
                if (shiftWidth.asBvConst.Value >= BigNum.FromInt(bitWidth))
                {
                    return new LiteralExpr(Token.NoToken, BigNum.FromInt(0), bitWidth);
                }
                else
                {
                    var result = ( valueToShift.asBvConst.Value.ToBigInteger >> shiftWidth.asBvConst.Value.ToIntSafe );
                    result = BigInteger.Remainder(result, BigInteger.Pow(2, bitWidth)); 
                    Debug.Assert(result < ( BigInteger.Pow(2, bitWidth) - 1 ));
                    return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), bitWidth);
                }
            }
            else
                return e;
        }

        public Expr Visit_bvashr(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var valueToShift = e.Args[0] as LiteralExpr;
                var shiftWidth = e.Args[1] as LiteralExpr;
                Debug.Assert(valueToShift.isBvConst);
                Debug.Assert(shiftWidth.isBvConst);
                Debug.Assert(valueToShift.asBvConst.Bits == shiftWidth.asBvConst.Bits);
                var bitWidth = ( valueToShift.asBvConst.Bits );

                // SMTLIBv2 definition is
                //     (bvashr s t) abbreviates
                //     (ite (= ((_ extract |m-1| |m-1|) s) #b0)
                //     (bvlshr s t)
                //     (bvnot (bvlshr (bvnot s) t)))


                var valueToShiftBI = valueToShift.asBvConst.Value.ToBigInteger;
                var shiftWidthBI = shiftWidth.asBvConst.Value.ToBigInteger;
                var threshold = BigInteger.Pow(2, bitWidth - 1);
                bool MSBIsZero = valueToShiftBI < threshold;

                if (shiftWidthBI >= bitWidth)
                {
                    return new LiteralExpr(Token.NoToken, BigNum.FromInt(0), bitWidth);
                }

                BigInteger result = 0;
                if (MSBIsZero)
                {
                    // Fold just like bvlshr
                    result = valueToShiftBI >> shiftWidth.asBvConst.Value.ToIntSafe;
                    result = BigInteger.Remainder(result, BigInteger.Pow(2, bitWidth));

                }
                else
                {
                    // Shift the inverted bit pattern
                    var invertedValueToShift = InvertDecimalReprBVBits(valueToShiftBI, bitWidth);
                    result = invertedValueToShift >> shiftWidth.asBvConst.Value.ToIntSafe;

                    // now invert back
                    result = InvertDecimalReprBVBits(result, bitWidth);
                    result = BigInteger.Remainder(result, BigInteger.Pow(2, bitWidth));
                }
                Debug.Assert(result <= ( BigInteger.Pow(2, bitWidth) - 1 ));
                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), bitWidth);

            }
            else
                return e;
        }

        public Expr Visit_bvult(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                Debug.Assert(arg1.isBvConst);

                if (arg0.asBvConst.Value < arg1.asBvConst.Value)
                    return Expr.True;
                else
                    return Expr.False;
            }
            else
                return e;
        }

        public Expr Visit_bvule(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                Debug.Assert(arg1.isBvConst);

                if (arg0.asBvConst.Value <= arg1.asBvConst.Value)
                    return Expr.True;
                else
                    return Expr.False;
            }
            else
                return e;
        }

        public Expr Visit_bvugt(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                Debug.Assert(arg1.isBvConst);

                if (arg0.asBvConst.Value > arg1.asBvConst.Value)
                    return Expr.True;
                else
                    return Expr.False;
            }
            else
                return e;
        }

        public Expr Visit_bvuge(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.isBvConst);
                Debug.Assert(arg1.isBvConst);

                if (arg0.asBvConst.Value >= arg1.asBvConst.Value)
                    return Expr.True;
                else
                    return Expr.False;
            }
            else
                return e;
        }

        public Expr Visit_bvslt(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var x = e.Args[0] as LiteralExpr;
                var y = e.Args[1] as LiteralExpr;
                Debug.Assert(x.asBvConst.Bits == y.asBvConst.Bits, "Bitwidth mismatch");

                // Check the sign of the bitvector in a two's complement representation
                var threshold = BigInteger.Pow(2, x.asBvConst.Bits - 1);

                bool xIsPositiveOrZero = x.asBvConst.Value.ToBigInteger < threshold;
                bool yIsPositiveOrZero = y.asBvConst.Value.ToBigInteger < threshold;

                if (xIsPositiveOrZero == yIsPositiveOrZero)
                {
                    // For this case with twos complement representation
                    //
                    // Notation: (x+ve) means x where x is a positive or zero bitvector under two's complement
                    //  _decimal_rep means the decimal representation of the bitvector treating it as unsigned
                    //
                    //
                    // (x+ve) < (y+ve) == (x_decimal_rep) < (y_decimal_rep)
                    // (x-ve) < (y-ve) == (x_decimal_rep) < (y_decimal_rep)

                    bool truth = x.asBvConst.Value < y.asBvConst.Value;

                    if (truth)
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else if (xIsPositiveOrZero && !yIsPositiveOrZero)
                {
                    // (x+ve) < (y-ve) == False
                    return Expr.False;
                }
                else if (!xIsPositiveOrZero && yIsPositiveOrZero)
                {
                    // (x-ve) < (y+ve) == True
                    return Expr.True;
                }
                else
                {
                    throw new InvalidProgramException("Unreachable!");
                }
            }
            else
                return e;
        }

        public Expr Visit_bvsle(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var x = e.Args[0] as LiteralExpr;
                var y = e.Args[1] as LiteralExpr;
                Debug.Assert(x.asBvConst.Bits == y.asBvConst.Bits, "Bitwidth mismatch");

                // Check the sign of the bitvector in a two's complement representation
                var threshold = BigInteger.Pow(2, x.asBvConst.Bits - 1);

                bool xIsPositiveOrZero = x.asBvConst.Value.ToBigInteger < threshold;
                bool yIsPositiveOrZero = y.asBvConst.Value.ToBigInteger < threshold;

                if (xIsPositiveOrZero == yIsPositiveOrZero)
                {
                    // For this case with twos complement representation
                    //
                    // Notation: (x+ve) means x where x is a positive or zero bitvector under two's complement
                    //  _decimal_rep means the decimal representation of the bitvector treating it as unsigned
                    //
                    //
                    // (x+ve) <= (y+ve) == (x_decimal_rep) <= (y_decimal_rep)
                    // (x-ve) <= (y-ve) == (x_decimal_rep) <= (y_decimal_rep)

                    bool truth = x.asBvConst.Value <= y.asBvConst.Value;

                    if (truth)
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else if (xIsPositiveOrZero && !yIsPositiveOrZero)
                {
                    // (x+ve) <= (y-ve) == False
                    return Expr.False;
                }
                else if (!xIsPositiveOrZero && yIsPositiveOrZero)
                {
                    // (x-ve) <= (y+ve) == True
                    return Expr.True;
                }
                else
                {
                    throw new InvalidProgramException("Unreachable!");
                }
            }
            else
                return e;
        }

        public Expr Visit_bvsgt(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var x = e.Args[0] as LiteralExpr;
                var y = e.Args[1] as LiteralExpr;
                Debug.Assert(x.asBvConst.Bits == y.asBvConst.Bits, "Bitwidth mismatch");

                // Check the sign of the bitvector in a two's complement representation
                var threshold = BigInteger.Pow(2, x.asBvConst.Bits - 1);

                bool xIsPositiveOrZero = x.asBvConst.Value.ToBigInteger < threshold;
                bool yIsPositiveOrZero = y.asBvConst.Value.ToBigInteger < threshold;

                if (xIsPositiveOrZero == yIsPositiveOrZero)
                {
                    // For this case with twos complement representation
                    //
                    // Notation: (x+ve) means x where x is a positive bitvector under two's complement
                    //  _decimal_rep means the decimal representation of the bitvector treating it as unsigned
                    //
                    //
                    // (x+ve) > (y+ve) == (x_decimal_rep) > (y_decimal_rep)
                    // (x-ve) > (y-ve) == (x_decimal_rep) > (y_decimal_rep)

                    bool truth = x.asBvConst.Value > y.asBvConst.Value;

                    if (truth)
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else if (xIsPositiveOrZero && !yIsPositiveOrZero)
                {
                    // (x+ve) > (y-ve) == True
                    return Expr.True;
                }
                else if (!xIsPositiveOrZero && yIsPositiveOrZero)
                {
                    // (x-ve) > (y+ve) == False
                    return Expr.False;
                }
                else
                {
                    throw new InvalidProgramException("Unreachable!");
                }
            }
            else
                return e;
        }

        public Expr Visit_bvsge(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var x = e.Args[0] as LiteralExpr;
                var y = e.Args[1] as LiteralExpr;
                Debug.Assert(x.asBvConst.Bits == y.asBvConst.Bits, "Bitwidth mismatch");

                // Check the sign of the bitvector in a two's complement representation
                var threshold = BigInteger.Pow(2, x.asBvConst.Bits - 1);

                bool xIsPositiveOrZero = x.asBvConst.Value.ToBigInteger < threshold;
                bool yIsPositiveOrZero = y.asBvConst.Value.ToBigInteger < threshold;

                if (xIsPositiveOrZero == yIsPositiveOrZero)
                {
                    // For this case with twos complement representation
                    //
                    // Notation: (x+ve) means x where x is a positive bitvector under two's complement
                    //  _decimal_rep means the decimal representation of the bitvector treating it as unsigned
                    //
                    //
                    // (x+ve) >= (y+ve) == (x_decimal_rep) >= (y_decimal_rep)
                    // (x-ve) >= (y-ve) == (x_decimal_rep) >= (y_decimal_rep)

                    bool truth = x.asBvConst.Value >= y.asBvConst.Value;

                    if (truth)
                        return Expr.True;
                    else
                        return Expr.False;
                }
                else if (xIsPositiveOrZero && !yIsPositiveOrZero)
                {
                    // (x+ve) >= (y-ve) == True
                    return Expr.True;
                }
                else if (!xIsPositiveOrZero && yIsPositiveOrZero)
                {
                    // (x-ve) >= (y+ve) == False
                    return Expr.False;
                }
                else
                {
                    throw new InvalidProgramException("Unreachable!");
                }
            }
            else
                return e;
        }
    }
}

