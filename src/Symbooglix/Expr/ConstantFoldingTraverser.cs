using System;
using Microsoft.Boogie;
using System.Diagnostics;
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

        public Expr VisitOldExpr(OldExpr e)
        {
            throw new NotImplementedException();
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
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr VisitDiv(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr VisitMod(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
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

            // FIXME: We should check for structural equivalence
            // we can't do this right now because Boogie's equals operator
            // overload is broken!

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

            // FIXME: We should check for structural equivalence
            // we can't do this right now because Boogie's equals operator
            // overload is broken!

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
                if (e.Args[0] is LiteralExpr)
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
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvudiv(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvurem(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvsdiv(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvsrem(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvsmod(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
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
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvand(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvor(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvnot(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 1);
            if (e.Args[0] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvxor(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvshl(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvlshr(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvashr(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
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
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvugt(NAryExpr e)
        {
            // FIXME: How are the signed operators going to work?
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

        public Expr Visit_bvuge(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvslt(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvsle(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvsgt(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }

        public Expr Visit_bvsge(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return e;
        }
    }
}

