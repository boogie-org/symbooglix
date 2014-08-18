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
        Expr BVOR(Expr lhs, Expr rhs);
        Expr BVSHL(Expr lhs, Expr rhs);

        // Real/Int operators

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

        public Expr BVSLT(Expr lhs, Expr rhs)
        {
            Debug.Assert(lhs.Type != null);
            Debug.Assert(rhs.Type != null);
            Debug.Assert(lhs.Type == rhs.Type);
            Debug.Assert(lhs.Type is BvType);

            int bits = lhs.Type.BvBits;

            // FIXME: Cache this for each bitwidth
            var builtinFunctionCall = CreateBVBuiltIn("BVSLT" + bits.ToString(),
                                                      "bvslt", BasicType.Bool,
                                                      new List<Microsoft.Boogie.Type>()
                                                      {
                                                        BasicType.GetBvType(bits),
                                                        BasicType.GetBvType(bits)
                                                      }
                                                     );

            var result = new NAryExpr(Token.NoToken, builtinFunctionCall, new List<Expr>() { lhs, rhs });
            return result;
        }

        public Expr BVOR(Expr lhs, Expr rhs)
        {
            Debug.Assert(lhs.Type != null);
            Debug.Assert(rhs.Type != null);
            Debug.Assert(lhs.Type == rhs.Type);
            Debug.Assert(lhs.Type is BvType);

            int bits = lhs.Type.BvBits;

            // FIXME: Cache this for each bitwidth
            var builtinFunctionCall = CreateBVBuiltIn("BVOR" + bits.ToString(),
                                                      "bvor", BasicType.GetBvType(bits),
                                                      new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(bits),
                BasicType.GetBvType(bits)
            }
                                                     );

            var result = new NAryExpr(Token.NoToken, builtinFunctionCall, new List<Expr>() { lhs, rhs });
            return result;
        }

        public Expr BVSHL(Expr lhs, Expr rhs)
        {
            Debug.Assert(lhs.Type != null);
            Debug.Assert(rhs.Type != null);
            Debug.Assert(lhs.Type == rhs.Type);
            Debug.Assert(lhs.Type is BvType);

            int bits = lhs.Type.BvBits;

            // FIXME: Cache this for each bitwidth
            var builtinFunctionCall = CreateBVBuiltIn("BVSHL" + bits.ToString(),
                                                      "bvshl", BasicType.GetBvType(bits),
                                                      new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(bits),
                BasicType.GetBvType(bits)
            }
                                                     );

            var result = new NAryExpr(Token.NoToken, builtinFunctionCall, new List<Expr>() { lhs, rhs });
            return result;
        }
    }
}

