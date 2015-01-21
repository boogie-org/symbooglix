using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.Collections.Generic;
using System.Collections.Concurrent;
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

        private ConcurrentDictionary<string, FunctionCall> CachedFunctions = new ConcurrentDictionary<string, FunctionCall>();
        private Expr GetBinaryBVFunction(Microsoft.Boogie.Type returnType, string NameWithoutSizeSuffx, string builtin, Expr lhs, Expr rhs)
        {
            if (!lhs.Type.IsBv)
            {
                throw new ExprTypeCheckException("lhs must be bitvector");
            }

            if (!rhs.Type.IsBv)
            {
                throw new ExprTypeCheckException("rhs must be bitvector");
            }

            if (lhs.Type != rhs.Type)
            {
                throw new ExprTypeCheckException("bitwidth mistmatch");
            }

            int bits = lhs.Type.BvBits;
            Debug.Assert(bits == rhs.Type.BvBits);

            var functionName = NameWithoutSizeSuffx + bits.ToString();
            FunctionCall builtinFunctionCall = null;
            try
            {
                builtinFunctionCall = CachedFunctions[functionName];
            }
            catch(KeyNotFoundException)
            {
                // Cache miss, build the FunctionCall
                builtinFunctionCall = CreateBVBuiltIn(functionName,
                    builtin, returnType, new List<Microsoft.Boogie.Type>()
                    {
                        BasicType.GetBvType(bits),
                        BasicType.GetBvType(bits)
                    });
                CachedFunctions[functionName] = builtinFunctionCall;
            }

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
            var result = GetBinaryBVFunction(lhs.Type, "BVOR", "bvor", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVAND(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVAND", "bvand", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVXOR(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVXOR", "bvxor", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVSHL(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVSHL", "bvshl", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVLSHR(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVLSHR", "bvlshr", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVASHR(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVASHR", "bvashr", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVADD(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVADD", "bvadd", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVMUL(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVMUL", "bvmul", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVUDIV(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVUDIV", "bvudiv", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVSDIV(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVSDIV", "bvsdiv", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVUREM(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVUREM", "bvurem", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVSREM(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVSREM", "bvsrem", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr BVSMOD(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVSMOD", "bvsmod", lhs, rhs);
            result.Type = lhs.Type;
            return result;
        }

        public Expr GetUnaryBVFunction(Microsoft.Boogie.Type returnType, string NameWithoutSizeSuffx, string builtin, Expr operand, bool getSuffixFromReturnType = false)
        {
            if (!operand.Type.IsBv)
            {
                throw new ExprTypeCheckException("operand must be BvType");
            }

            int bits = 0;

            if (getSuffixFromReturnType)
            {
                if (!returnType.IsBv)
                    throw new ArgumentException("expected return type to be BvType");
                bits = returnType.BvBits;
            }
            else
            {
                bits = operand.Type.BvBits;
            }

            var functionName = NameWithoutSizeSuffx + bits.ToString();
            FunctionCall builtinFunctionCall = null;
            try
            {
                builtinFunctionCall = CachedFunctions[functionName];
            }
            catch (KeyNotFoundException)
            {
                // Cache miss, build the FunctionCall
                builtinFunctionCall = CreateBVBuiltIn(functionName,
                    builtin, returnType, new List<Microsoft.Boogie.Type>()
                    {
                        BasicType.GetBvType(bits)
                    });
                CachedFunctions[functionName] = builtinFunctionCall;
            }

            var result = new NAryExpr(Token.NoToken, builtinFunctionCall, new List<Expr>() { operand});
            return result;
        }

        public Expr BVNEG(Expr operand)
        {
            var result = GetUnaryBVFunction(operand.Type, "BVNEG", "bvneg", operand);
            result.Type = operand.Type;
            return result;
        }

        public Expr BVNOT(Expr operand)
        {
            var result = GetUnaryBVFunction(operand.Type, "BVNOT", "bvnot", operand);
            result.Type = operand.Type;
            return result;

        }

        public Expr BVSEXT(Expr operand, int newWidth)
        {
            if (!operand.Type.IsBv)
            {
                throw new ExprTypeCheckException("operand must be BvType");
            }

            int originalWidth = operand.Type.BvBits;

            if (newWidth < originalWidth)
            {
                throw new ArgumentException("newWidth must be greater than the operand's bit width");
            }

            var functionNameWithoutSuffix = string.Format("BV{0}_SEXT", originalWidth);
            var builtinName = string.Format("sign_extend {0}", ( newWidth - originalWidth ));
            var newType = BasicType.GetBvType(newWidth);
            var result = GetUnaryBVFunction(newType, functionNameWithoutSuffix, builtinName, operand, /*getSuffixFromReturnType=*/ true);
            result.Type = newType;
            return result;
        }

        public Expr BVZEXT(Expr operand, int newWidth)
        {
            if (!operand.Type.IsBv)
            {
                throw new ExprTypeCheckException("operand must be BvType");
            }

            int originalWidth = operand.Type.BvBits;

            if (newWidth < originalWidth)
            {
                throw new ArgumentException("newWidth must be greater than the operand's bit width");
            }

            var functionNameWithoutSuffix = string.Format("BV{0}_ZEXT", originalWidth);
            var builtinName = string.Format("zero_extend {0}", ( newWidth - originalWidth ));
            var newType = BasicType.GetBvType(newWidth);
            var result = GetUnaryBVFunction(newType, functionNameWithoutSuffix, builtinName, operand, /*getSuffixFromReturnType=*/ true);
            result.Type = newType;
            return result;
        }

        public Expr BVCONCAT(Expr MSB, Expr LSB)
        {
            if (!MSB.Type.IsBv)
            {
                throw new ExprTypeCheckException("MSB must be BvType");
            }

            if (!LSB.Type.IsBv)
            {
                throw new ExprTypeCheckException("MSB must be BvType");
            }

            var result = new BvConcatExpr(Token.NoToken, MSB, LSB);
            result.Type = result.ShallowType;
            return result;
        }

        public Expr BVEXTRACT(Expr operand, int end, int start)
        {
            if (!operand.Type.IsBv)
            {
                throw new ExprTypeCheckException("operand must be BvType");
            }

            if (end <= start)
            {
                throw new ArgumentException("end must be > start");
            }

            if (start < 0)
            {
                throw new ArgumentException("start must be >= 0");
            }

            if (end >= operand.Type.BvBits)
            {
                throw new ArgumentException("end must be < the bit width of the operand");
            }

            var result = new BvExtractExpr(Token.NoToken, operand, end, start);
            result.Type = result.ShallowType;
            return result;
        }

        private ConcurrentDictionary<BinaryOperator.Opcode, BinaryOperator> BinaryOperatorCache = new ConcurrentDictionary<BinaryOperator.Opcode, BinaryOperator>();
        private IAppliable GetBinaryFunction(BinaryOperator.Opcode oc)
        {
            BinaryOperator function = null;
            try
            {
                function = BinaryOperatorCache[oc];
            }
            catch (KeyNotFoundException)
            {
                function = new BinaryOperator(Token.NoToken, oc);
                BinaryOperatorCache[oc] = function;
            }
            return function;
        }

        public Expr NotEq(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs type must be the same");
            }
            var result = new NAryExpr(Token.NoToken, GetBinaryFunction(BinaryOperator.Opcode.Neq) , new List<Expr> { lhs, rhs });
            result.Type = BasicType.Bool;
            return result;
        }

        public Expr Eq(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs type must be the same");
            }
            var result = new NAryExpr(Token.NoToken, GetBinaryFunction(BinaryOperator.Opcode.Eq), new List<Expr> { lhs, rhs });
            result.Type = BasicType.Bool;
            return result;
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
