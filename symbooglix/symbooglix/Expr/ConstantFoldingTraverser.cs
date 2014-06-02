using System;
using Microsoft.Boogie;
using System.Diagnostics;
using Action = symbooglix.Traverser.Action;
using System.Numerics;
using Microsoft.Basetypes;

namespace symbooglix
{
    // Clients should use this.
    public class ConstantFoldingTraverser : DFSPostOrderTraverser
    {
        public ConstantFoldingTraverser() : base( new ConstantFoldingVisitor() ) { }
    }

    public class ConstantFoldingVisitor : IExprVisitor
    {
        public Action VisitLiteralExpr(LiteralExpr e)
        {
            // Can't constant fold a literal
            return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitIdentifierExpr(IdentifierExpr e)
        {
            // This is a symbolic variable so we can't constant fold
            return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitOldExpr(OldExpr e)
        {
            throw new NotImplementedException();
        }

        public Action VisitCodeExpr(CodeExpr e)
        {
            throw new NotImplementedException();
        }

        public Action VisitBvExtractExpr(BvExtractExpr e)
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
                return Traverser.Action.ContinueTraversal(resultExpr);
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitBvConcatExpr(BvConcatExpr e)
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
                return Traverser.Action.ContinueTraversal(result);
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitForallExpr(ForallExpr e)
        {
            // ∀ x : true  <==> true
            // ∀ x : false  <==> false
            if (e.Body is LiteralExpr)
            {
                var literal = (LiteralExpr) e.Body;
                Debug.Assert(literal.isBool);
                return Traverser.Action.ContinueTraversal(literal);
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitExistExpr(ExistsExpr e)
        {
            // ∃ x : true  <==> true
            // ∃ x : false  <==> false
            if (e.Body is LiteralExpr)
            {
                var literal = (LiteralExpr) e.Body;
                Debug.Assert(literal.isBool);
                return Traverser.Action.ContinueTraversal(literal);
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitLambdaExpr(LambdaExpr e)
        {
            // We can't constant fold these.
            return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitNot(NAryExpr e)
        {
            if (e.Args[0] is LiteralExpr)
            {
                var literal = (LiteralExpr) e.Args[0];
                if (literal.IsTrue)
                    return Traverser.Action.ContinueTraversal(Expr.False);
                else if (literal.IsFalse)
                    return Traverser.Action.ContinueTraversal(Expr.True);
                else
                    throw new Exception("Invalid operand to Not");
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitNeg(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 1);
            if (e.Args[0] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitAdd(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitSub(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitMul(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitDiv(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitMod(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitRealDiv(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitEq(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                // FIXME: We can't implement this nicely
                // right now because equality comparision
                // of Expr is totally broken in Boogie!
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitNeq(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                // FIXME: We can't implement this nicely
                // right now because equality comparision
                // of Expr is totally broken in Boogie!
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitGt(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitGe(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitLt(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitLe(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                throw new NotImplementedException();
            }
            else
                return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitAnd(NAryExpr e)
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
                        return Traverser.Action.ContinueTraversal(Expr.False);
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
                    return Traverser.Action.ContinueTraversal(Expr.True);
            }

            return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitOr(NAryExpr e)
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
                        return Traverser.Action.ContinueTraversal(Expr.True);
                }
            }

            // false OR false == false
            if (e.Args[0] is LiteralExpr && e.Args[1] is LiteralExpr)
            {
                var arg0 = e.Args[0] as LiteralExpr;
                var arg1 = e.Args[1] as LiteralExpr;
                Debug.Assert(arg0.IsFalse && arg1.IsFalse);
                return Traverser.Action.ContinueTraversal(Expr.False);
            }

            // Can't constant fold
            return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitImp(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2);

            if (e.Args[0] is LiteralExpr)
            {
                var literal = e.Args[0] as LiteralExpr;
                Debug.Assert(literal.isBool);

                // true -> <expr> == <expr>
                if (literal.IsTrue)
                    return Traverser.Action.ContinueTraversal(e.Args[1]);
                // false -> <expr> == true
                else if (literal.IsFalse)
                    return Traverser.Action.ContinueTraversal(Expr.True);
            }

            // can't constant fold
            return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitIff(NAryExpr e)
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
                    return Traverser.Action.ContinueTraversal(Expr.True);
                }
                else
                {
                    // (true <==> false) == false
                    // (false <==> true) == false
                    return Traverser.Action.ContinueTraversal(Expr.False);
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
                        return Traverser.Action.ContinueTraversal(e.Args[otherIndex]);
                    }
                    else
                    {
                        Debug.Assert(literal.IsFalse);
                        // (false <==> <expr>) == not <expr>
                        // (<expr> <==> false) == not <expr>
                        return Traverser.Action.ContinueTraversal(Expr.Not(e.Args[otherIndex]));
                    }
                }
            }

            // otherwise we can't constant fold
            return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitSubType(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action VisitMapStore(NAryExpr e)
        {
            // Can't do any constant folding without access execution state
            return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitMapSelect(NAryExpr e)
        {
            // Can't do any constant folding without access execution state
            return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitIfThenElse(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action VisitFunctionCall(NAryExpr e)
        {
            // The executor should (at some point)
            // make sure that Functions
            // that can be inlined already have been so
            // we shouldn't need to do anything.
            return Traverser.Action.ContinueTraversal(e);
        }

        public Action VisitTypeCoercion(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action VisitArithmeticCoercion(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvadd(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvsub(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvmul(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvudiv(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvurem(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvsdiv(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvsrem(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvsmod(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_sign_extend(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_zero_extend(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvneg(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvand(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvor(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvnot(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvxor(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvshl(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvlshr(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvashr(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvult(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvule(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvugt(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvuge(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvslt(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvsle(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvsgt(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Action Visit_bvsge(NAryExpr e)
        {
            throw new NotImplementedException();
        }
    }
}

