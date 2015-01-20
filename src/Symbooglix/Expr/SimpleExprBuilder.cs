using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.Collections.Generic;
using System.Diagnostics;
using System.Numerics;

namespace Symbooglix
{
    public class SimpleExprBuilder : IExprBuilder
    {
        public FunctionCall CreateBVBuiltIn(string Name, string Builtin, Microsoft.Boogie.Type returnType, IList<Microsoft.Boogie.Type> argTypes)
        {
            var funcCall = CreateFunctionCall(Name, returnType, argTypes);
            funcCall.Func.AddAttribute("bvbuiltin", new string[] { Builtin });
            return funcCall;
        }

        public FunctionCall CreateFunctionCall(string Name, Microsoft.Boogie.Type returnType, IList<Microsoft.Boogie.Type> argTypes)
        {
            var returnVar = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", returnType), false);
            var vars = new List<Variable>();
            foreach (var T in argTypes)
            {
                vars.Add( new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "",T), true));
            }

            // Finally build the function and the function call
            var funcCall = new FunctionCall(new Function(Token.NoToken, Name, vars, returnVar));
            return funcCall;
        }

        public LiteralExpr ConstantInt(int value)
        {
            return new LiteralExpr(Token.NoToken, BigNum.FromInt(value));
        }

        public LiteralExpr ConstantReal(string value)
        {
            return new LiteralExpr(Token.NoToken, BigDec.FromString(value));
        }

        public LiteralExpr ConstantBool(bool value)
        {
            return new LiteralExpr(Token.NoToken, value);
        }

        public LiteralExpr ConstantBV(int decimalValue, int bitWidth)
        {
            return ConstantBV(new BigInteger(decimalValue), bitWidth);
        }

        public LiteralExpr True
        {
            get 
            {
                return ConstantBool(true);
            }
        }

        public LiteralExpr False 
        {
            get
            {
                return ConstantBool(false);
            }
        }

        public LiteralExpr ConstantBV(BigInteger decimalValue, int bitWidth)
        {
            var twoToPowerOfBits = BigInteger.Pow(2, bitWidth);
            if (decimalValue.Sign < 0)
            {
                // Convert the decimal value into two's complement representation
                //
                // The rule is basically this:
                //
                // decimal_rep_for_bits = (2^m - x) mod (2^m)

                if (bitWidth <=1)
                    throw new ArgumentException("Decimal value cannot be represented in the requested number of bits");

                var abs = BigInteger.Abs(decimalValue);

                if (abs >= BigInteger.Pow(2, bitWidth -1))
                    throw new ArgumentException("Decimal value cannot be represented in the requested number of bits");

                var result = ( twoToPowerOfBits - abs );
                Debug.Assert(result > 0);

                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), bitWidth);
            }
            else
            {
                if (bitWidth < 1)
                    throw new ArgumentException("Bitwidth must be >= 1");

                // Positive or zero
                if (decimalValue >= twoToPowerOfBits)
                    throw new ArgumentException("Decimal value cannot be represented in the requested number of bits");

                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(decimalValue), bitWidth);
            }
        }

        private Expr GetBinaryBVFunction(Microsoft.Boogie.Type returnType, string NameWithoutSizeSuffx, string builtin, Expr lhs, Expr rhs)
        {
            if (!lhs.Type.IsBv)
            {
                throw new ExprTypeCheckException("lhs must be bitvector");
            }

            if (!rhs.Type.IsBv)
            {
                throw new ExprTypeCheckException("lhs must be bitvector");
            }

            if (lhs.Type != rhs.Type)
            {
                throw new ExprTypeCheckException("bitwidth mistmatch");
            }

            int bits = lhs.Type.BvBits;
            Debug.Assert(bits == rhs.Type.BvBits);

            // FIXME: Cache this for each bitwidth
            var builtinFunctionCall = CreateBVBuiltIn(NameWithoutSizeSuffx + bits.ToString(),
                                                          builtin, returnType,
                                                          new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(bits),
                BasicType.GetBvType(bits)
            }
                                                         );

            var result = new NAryExpr(Token.NoToken, builtinFunctionCall, new List<Expr>() { lhs, rhs });
            return result;
        }

        public Expr BVSLT(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.Bool, "BVSLT", "bvslt", lhs, rhs);
            result.Type = Microsoft.Boogie.Type.Bool;
            return result;
        }

        public Expr BVSLE (Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.Bool, "BVSLE", "bvsle", lhs, rhs);
            result.Type = Microsoft.Boogie.Type.Bool;
            return result;
        }

        public Expr BVSGT(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.Bool, "BVSGT", "bvsgt", lhs, rhs);
            result.Type = Microsoft.Boogie.Type.Bool;
            return result;
        }

        public Expr BVSGE(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.Bool, "BVSGE", "bvsge", lhs, rhs);
            result.Type = Microsoft.Boogie.Type.Bool;
            return result;
        }

        public Expr BVULT(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.Bool, "BVULT", "bvult", lhs, rhs);
            result.Type = Microsoft.Boogie.Type.Bool;
            return result;
        }

        public Expr BVULE(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.Bool, "BVULE", "bvule", lhs, rhs);
            result.Type = Microsoft.Boogie.Type.Bool;
            return result;
        }

        public Expr BVUGT(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.Bool, "BVUGT", "bvugt", lhs, rhs);
            result.Type = Microsoft.Boogie.Type.Bool;
            return result;
        }

        public Expr BVUGE(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.Bool, "BVUGE", "bvuge", lhs, rhs);
            result.Type = Microsoft.Boogie.Type.Bool;
            return result;
        }

        public Expr BVOR(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVOR", "bvor", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVAND(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVAND", "bvand", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVXOR(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVXOR", "bvxor", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVSHL(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVSHL", "bvshl", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVLSHR(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVLSHR", "bvlshr", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVASHR(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVASHR", "bvashr", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVADD(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVADD", "bvadd", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVMUL(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVMUL", "bvmul", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVUDIV(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVUDIV", "bvudiv", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVSDIV(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVSDIV", "bvsdiv", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVUREM(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVUREM", "bvurem", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVSREM(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVSREM", "bvsrem", lhs, rhs);
        }

        public Expr BVSMOD(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVSMOD", "bvsmod", lhs, rhs);
        }

        public Expr GetUnaryBVFunction(Microsoft.Boogie.Type returnType, string NameWithoutSizeSuffx, string builtin, Expr operand)
        {
            Debug.Assert(operand.Type != null);
            Debug.Assert(operand.Type is BvType);

            int bits = operand.Type.BvBits;

            // FIXME: Cache this for each bitwidth
            var builtinFunctionCall = CreateBVBuiltIn(NameWithoutSizeSuffx + bits.ToString(),
                                                          builtin, returnType,
                                                          new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(bits)
            }
                                                         );

            var result = new NAryExpr(Token.NoToken, builtinFunctionCall, new List<Expr>() { operand});
            return result;
        }

        public Expr BVNEG(Expr operand)
        {
            return GetUnaryBVFunction(BasicType.GetBvType(operand.Type.BvBits), "BVNEG", "bvneg", operand);

        }

        public Expr BVNOT(Expr operand)
        {
            return GetUnaryBVFunction(BasicType.GetBvType(operand.Type.BvBits), "BVNOT", "bvnot", operand);

        }

        public Expr NotEq(Expr lhs, Expr rhs)
        {
            // FIXME: Factor some of this out.
            // FIXME: Cache operators
            return new NAryExpr(Token.NoToken, new BinaryOperator(Token.NoToken,BinaryOperator.Opcode.Neq), new List<Expr> { lhs, rhs });
        }

        public Expr Eq(Expr lhs, Expr rhs)
        {
            // FIXME: Factor some of this out.
            // FIXME: Cache operators
            return new NAryExpr(Token.NoToken, new BinaryOperator(Token.NoToken,BinaryOperator.Opcode.Eq), new List<Expr> { lhs, rhs });
        }

        public Expr Iff(Expr lhs, Expr rhs)
        {
            // FIXME: Factor some of this out.
            // FIXME: Cache operators
            return new NAryExpr(Token.NoToken, new BinaryOperator(Token.NoToken,BinaryOperator.Opcode.Iff), new List<Expr> { lhs, rhs });
        }

        public Expr And(Expr lhs, Expr rhs)
        {
            // FIXME: Factor some of this out.
            // FIXME: Cache operators
            return new NAryExpr(Token.NoToken, new BinaryOperator(Token.NoToken,BinaryOperator.Opcode.And), new List<Expr> { lhs, rhs });
        }

        public Expr Or (Expr lhs, Expr rhs)
        {
            // FIXME: Factor some of this out.
            // FIXME: Cache operators
            return new NAryExpr(Token.NoToken, new BinaryOperator(Token.NoToken,BinaryOperator.Opcode.Or), new List<Expr> { lhs, rhs });
        }

        public Expr IfThenElse (Expr condition, Expr thenExpr, Expr elseExpr)
        {
            // FIXME: Factor some of this out.
            // FIXME: Cache operators
            return new NAryExpr(Token.NoToken, new Microsoft.Boogie.IfThenElse(Token.NoToken), new List<Expr> { condition, thenExpr, elseExpr });
        }

        public Expr Not(Expr e)
        {
            // FIXME: Factor some of this out.
            // FIXME: Cache operators
            return new NAryExpr(Token.NoToken, new UnaryOperator(Token.NoToken, UnaryOperator.Opcode.Not), new List<Expr> { e });
        }
    }
}
