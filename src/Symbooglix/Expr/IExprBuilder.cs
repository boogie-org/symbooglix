using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.Collections.Generic;
using System.Diagnostics;
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

    public class ExprBuilder : IExprBuilder
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
            return ConstantBV(BigNum.FromInt(decimalValue), bitWidth);
        }

        public LiteralExpr ConstantBV(BigNum decimalValue, int bitWidth)
        {
            var twoToPowerOfBits = BigInteger.Pow(2, bitWidth);
            if (decimalValue.Signum < 0)
            {
                // Convert the decimal value into two's complement representation
                //
                // The rule is basically this:
                //
                // decimal_rep_for_bits = (2^m - x) mod (2^m)
                var abs = decimalValue.Abs.ToBigInteger;
                var result = ( twoToPowerOfBits - abs );
                Debug.Assert(result >= 0, "Decimal value cannot be represented in the requested number of bits");
                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), bitWidth);
            }
            else
            {
                // Positive or zero
                Debug.Assert( decimalValue.ToBigInteger < twoToPowerOfBits, "Decimal Value cannot be represented in the requested number of bits");
                return new LiteralExpr(Token.NoToken, decimalValue, bitWidth);
            }
        }

        private Expr GetBinaryBVFunction(Microsoft.Boogie.Type returnType, string NameWithoutSizeSuffx, string builtin, Expr lhs, Expr rhs)
        {
            Debug.Assert(lhs.Type != null);
            Debug.Assert(rhs.Type != null);
            Debug.Assert(lhs.Type == rhs.Type);
            Debug.Assert(lhs.Type is BvType);
            Debug.Assert(rhs.Type is BvType);

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
            return GetBinaryBVFunction(BasicType.Bool, "BVSLT", "bvslt", lhs, rhs);
        }

        public Expr BVSLE (Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.Bool, "BVSLE", "bvsle", lhs, rhs);
        }

        public Expr BVSGT(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.Bool, "BVSGT", "bvsgt", lhs, rhs);
        }

        public Expr BVSGE(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.Bool, "BVSGE", "bvsge", lhs, rhs);
        }

        public Expr BVOR(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVOR", "bvor", lhs, rhs);
        }

        public Expr BVAND(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVAND", "bvand", lhs, rhs);
        }

        public Expr BVXOR(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVXOR", "bvxor", lhs, rhs);
        }

        public Expr BVSHL(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVSHL", "bvshl", lhs, rhs);
        }

        public Expr BVLSHR(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVLSHR", "bvlshr", lhs, rhs);
        }

        public Expr BVASHR(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVASHR", "bvashr", lhs, rhs);
        }

        public Expr BVMUL(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVMUL", "bvmul", lhs, rhs);
        }

        public Expr BVUDIV(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVUDIV", "bvudiv", lhs, rhs);
        }

        public Expr BVSDIV(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVSDIV", "bvsdiv", lhs, rhs);
        }

        public Expr BVUREM(Expr lhs, Expr rhs)
        {
            return GetBinaryBVFunction(BasicType.GetBvType(lhs.Type.BvBits), "BVUREM", "bvurem", lhs, rhs);
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

