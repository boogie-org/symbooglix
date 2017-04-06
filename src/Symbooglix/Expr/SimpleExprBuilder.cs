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
using System.Collections.Concurrent;
using System.Diagnostics;
using System.Numerics;
using System.Linq;

namespace Symbooglix
{
    public class SimpleExprBuilder : IExprBuilder
    {
        FunctionCallBuilder FCB;
        private readonly bool _Immutable;
        public bool Immutable
        {
            get { return _Immutable; }
        }
        public SimpleExprBuilder(bool immutable)
        {
            FCB = new FunctionCallBuilder();
            _Immutable = immutable;
        }

        private FunctionCall CreateBVBuiltIn(string Name, string Builtin, Microsoft.Boogie.Type returnType, IList<Microsoft.Boogie.Type> argTypes)
        {
            // Skip the cache as we implement a cache elsewhere for bv operators
            var funcCall = FCB.CreateUninterpretedFunctionCall(Name, returnType, argTypes);
            funcCall.Func.AddAttribute("bvbuiltin", new string[] { Builtin });
            return funcCall;
        }

        private FunctionCall CreateBuiltIn(string name, string builtin, Microsoft.Boogie.Type returnType, IList<Microsoft.Boogie.Type> argTypes)
        {
            // Skip the cache as we implement a cache elsewhere for bv operators
            var funcCall = FCB.CreateUninterpretedFunctionCall(name, returnType, argTypes);
            funcCall.Func.AddAttribute("builtin", new string[] { builtin });
            return funcCall;
        }

        private NAryExpr GetNAry(IAppliable fun, List<Expr> args)
        {
            return new NAryExpr(Token.NoToken, fun, args, Immutable);
        }

        public LiteralExpr ConstantInt(int value)
        {
            return new LiteralExpr(Token.NoToken, BigNum.FromInt(value), Immutable);
        }

        public LiteralExpr ConstantInt(BigInteger decimalValue)
        {
            return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(decimalValue), Immutable);
        }

        public LiteralExpr ConstantReal(string value)
        {
            return new LiteralExpr(Token.NoToken, BigDec.FromString(value), Immutable);
        }

        public LiteralExpr ConstantReal(Microsoft.Basetypes.BigDec value)
        {
            return new LiteralExpr(Token.NoToken, value, Immutable);
        }

        public LiteralExpr ConstantBool(bool value)
        {
            return new LiteralExpr(Token.NoToken, value, Immutable);
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

        public Expr Identifier(Variable v)
        {
            return new IdentifierExpr(Token.NoToken, v, Immutable);
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
                // decimal_rep_for_bits = (2^m - |x|) mod (2^m)

                if (bitWidth <=1)
                    throw new ArgumentException("Decimal value cannot be represented in the requested number of bits");

                var abs = BigInteger.Abs(decimalValue);

                if (abs > BigInteger.Pow(2, bitWidth -1))
                    throw new ArgumentException("Decimal value cannot be represented in the requested number of bits");

                var result = ( twoToPowerOfBits - abs );
                Debug.Assert(result > 0);

                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(result), bitWidth, Immutable);
            }
            else
            {
                if (bitWidth < 1)
                    throw new ArgumentException("Bitwidth must be >= 1");

                // Positive or zero
                if (decimalValue >= twoToPowerOfBits)
                    throw new ArgumentException("Decimal value cannot be represented in the requested number of bits");

                return new LiteralExpr(Token.NoToken, BigNum.FromBigInt(decimalValue), bitWidth, Immutable);
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

            if (!lhs.Type.Equals(rhs.Type))
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

            var result = GetNAry(builtinFunctionCall, new List<Expr>() { lhs, rhs });
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

        public Expr BVSUB(Expr lhs, Expr rhs)
        {
            var result = GetBinaryBVFunction(lhs.Type, "BVSUB", "bvsub", lhs, rhs);
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

            int bits = operand.Type.BvBits;
            string suffixString = null;
            if (getSuffixFromReturnType)
            {
                if (!returnType.IsBv)
                    throw new ArgumentException("expected return type to be BvType");
                suffixString = returnType.BvBits.ToString();
            }
            else
            {
                suffixString = bits.ToString();
            }

            var functionName = NameWithoutSizeSuffx + suffixString;
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

            var result = GetNAry(builtinFunctionCall, new List<Expr>() { operand});
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

            var result = new BvConcatExpr(Token.NoToken, MSB, LSB, Immutable);
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

            if (end > operand.Type.BvBits)
            {
                throw new ArgumentException("end must be <= the bit width of the operand");
            }

            var result = new BvExtractExpr(Token.NoToken, operand, end, start, Immutable);
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
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Neq), new List<Expr> { lhs, rhs });
            result.Type = BasicType.Bool;
            return result;
        }

        public Expr Eq(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs type must be the same");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Eq), new List<Expr> { lhs, rhs });
            result.Type = BasicType.Bool;
            return result;
        }

        public Expr Iff(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.IsBool)
            {
                throw new ExprTypeCheckException("lhs must be bool");
            }

            if (!rhs.Type.IsBool)
            {
                throw new ExprTypeCheckException("rhs must be bool");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Iff), new List<Expr> { lhs, rhs });
            result.Type = BasicType.Bool;
            return result;
        }

        public Expr Imp(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.IsBool)
            {
                throw new ExprTypeCheckException("lhs must be bool");
            }

            if (!rhs.Type.IsBool)
            {
                throw new ExprTypeCheckException("rhs must be bool");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Imp), new List<Expr> { lhs, rhs });
            result.Type = BasicType.Bool;
            return result;
        }

        public Expr And(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.IsBool)
            {
                throw new ExprTypeCheckException("lhs must be bool");
            }

            if (!rhs.Type.IsBool)
            {
                throw new ExprTypeCheckException("rhs must be bool");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.And), new List<Expr> { lhs, rhs });
            result.Type = BasicType.Bool;
            return result;
        }

        public Expr Or(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.IsBool)
            {
                throw new ExprTypeCheckException("lhs must be bool");
            }

            if (!rhs.Type.IsBool)
            {
                throw new ExprTypeCheckException("rhs must be bool");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Or), new List<Expr> { lhs, rhs });
            result.Type = BasicType.Bool;
            return result;
        }

        private Microsoft.Boogie.IfThenElse IfThenElseCached = new Microsoft.Boogie.IfThenElse(Token.NoToken);
        public Expr IfThenElse(Expr condition, Expr thenExpr, Expr elseExpr)
        {
            if (!condition.Type.IsBool)
            {
                throw new ExprTypeCheckException("Condition must be bool");
            }

            if (!thenExpr.Type.Equals(elseExpr.Type))
            {
                throw new ExprTypeCheckException("thenExpr and elseExpr types must match");
            }
            var result = GetNAry(IfThenElseCached, new List<Expr> { condition, thenExpr, elseExpr });
            result.Type = thenExpr.Type;
            return result;
        }

        private ConcurrentDictionary<UnaryOperator.Opcode, UnaryOperator> UnaryOperatorCache = new ConcurrentDictionary<UnaryOperator.Opcode, UnaryOperator>();
        private IAppliable GetUnaryFunction(UnaryOperator.Opcode op)
        {
            UnaryOperator function = null;
            try
            {
                function = UnaryOperatorCache[op];
            }
            catch (KeyNotFoundException)
            {
                function = new UnaryOperator(Token.NoToken, op);
                UnaryOperatorCache[op] = function;
            }
            return function;
        }

        public Expr Not(Expr e)
        {
            if (!e.Type.IsBool)
            {
                throw new ExprTypeCheckException("expr must be bool");
            }
            var result = GetNAry(GetUnaryFunction(UnaryOperator.Opcode.Not), new List<Expr> { e });
            result.Type = BasicType.Bool;
            return result;
        }

        public Expr UFC(FunctionCall func, params Expr[] args)
        {
            if (args.Length != func.Func.InParams.Count)
            {
                throw new ExprTypeCheckException("Wrong number of arguments for supplied FunctionCall");
            }

            // Check type matches
            for (int index=0; index < args.Length; ++index)
            {
                if (!( args[index].Type.Equals(func.Func.InParams[index].TypedIdent.Type) ))
                {
                    throw new ExprTypeCheckException("Type mismatch between supplied FunctionCall and argument at index " + index.ToString());
                }
            }

            var result = GetNAry(func, new List<Expr>(args));
            result.Type = func.Func.OutParams[0].TypedIdent.Type;
            return result;
        }

        public Expr Add(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs must be the same type");
            }

            if (!lhs.Type.IsInt && !lhs.Type.IsReal)
            {
                throw new ExprTypeCheckException("lhs and rhs must both be of real or int type");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Add), new List<Expr>() { lhs, rhs });
            result.Type = lhs.Type;
            return result;
        }

        public Expr Sub(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs must be the same type");
            }

            if (!lhs.Type.IsInt && !lhs.Type.IsReal)
            {
                throw new ExprTypeCheckException("lhs and rhs must both be of real or int type");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Sub), new List<Expr>() { lhs, rhs });
            result.Type = lhs.Type;
            return result;
        }

        public Expr Mul(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs must be the same type");
            }

            if (!lhs.Type.IsInt && !lhs.Type.IsReal)
            {
                throw new ExprTypeCheckException("lhs and rhs must both be of real or int type");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Mul), new List<Expr>() { lhs, rhs });
            result.Type = lhs.Type;
            return result;
        }

        public Expr Div(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs must be the same type");
            }

            if (!lhs.Type.IsInt)
            {
                throw new ExprTypeCheckException("lhs and rhs must both be of int type");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Div), new List<Expr>() { lhs, rhs });
            result.Type = BasicType.Int;
            return result;
        }

        public Expr RealDiv(Expr lhs, Expr rhs)
        {
            // Boogie's Type checker seems to allow operands of mixed types. I really don't like this.
            // I'd much rather enforce that args being of type (int, int) or (real, real).
            if (!lhs.Type.IsInt && !lhs.Type.IsReal)
            {
                throw new ExprTypeCheckException("lhs and rhs must be of real or int type");
            }
            if (!rhs.Type.IsInt && !rhs.Type.IsReal)
            {
                throw new ExprTypeCheckException("rhs and rhs must be of real or int type");
            }

            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.RealDiv), new List<Expr>() { lhs, rhs });
            result.Type = BasicType.Real;
            return result;
        }

        public Expr Mod(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs must be the same type");
            }

            if (!lhs.Type.IsInt)
            {
                throw new ExprTypeCheckException("lhs and rhs must both be of int type");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Mod), new List<Expr>() { lhs, rhs });
            result.Type = BasicType.Int;
            return result;
        }

        // This is a Z3 extension and isn't a core operator in Boogie's Expr language
        public Expr Rem(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs must be the same type");
            }

            if (!lhs.Type.IsInt)
            {
                throw new ExprTypeCheckException("lhs and rhs must both be of int type");
            }

            // Try to get from cache
            FunctionCall function = null;
            try
            {
                function = CachedFunctions["rem"];
            }
            catch (KeyNotFoundException)
            {
                function = CreateBuiltIn("rem", "rem", BasicType.Int, new List<Microsoft.Boogie.Type>() {BasicType.Int, BasicType.Int});
                CachedFunctions["rem"] = function;
            }

            var result = GetNAry(function, new List<Expr>() { lhs, rhs });
            result.Type = BasicType.Int;
            return result;
        }

        public Expr Pow(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs must be the same type");
            }

            if (!lhs.Type.IsReal)
            {
                throw new ExprTypeCheckException("lhs and rhs must both be of real type");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Pow), new List<Expr>() { lhs, rhs });
            result.Type = BasicType.Real;
            return result;
        }

        public Expr Neg(Expr operand)
        {
            if (!operand.Type.IsInt && !operand.Type.IsReal)
            {
                throw new ExprTypeCheckException("operand must be real or int");
            }

            var result = GetNAry(GetUnaryFunction(UnaryOperator.Opcode.Neg), new List<Expr>() { operand });
            result.Type = operand.Type;
            return result;
        }

        public Expr Lt(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs must be the same type");
            }

            if (!lhs.Type.IsInt && !lhs.Type.IsReal)
            {
                throw new ExprTypeCheckException("lhs and rhs must both be of int type or real type");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Lt), new List<Expr>() { lhs, rhs });
            result.Type = BasicType.Bool;
            return result;
        }

        public Expr Le(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs must be the same type");
            }

            if (!lhs.Type.IsInt && !lhs.Type.IsReal)
            {
                throw new ExprTypeCheckException("lhs and rhs must both be of int type or real type");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Le), new List<Expr>() { lhs, rhs });
            result.Type = BasicType.Bool;
            return result;
        }

        public Expr Gt(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs must be the same type");
            }

            if (!lhs.Type.IsInt && !lhs.Type.IsReal)
            {
                throw new ExprTypeCheckException("lhs and rhs must both be of int type or real type");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Gt), new List<Expr>() { lhs, rhs });
            result.Type = BasicType.Bool;
            return result;
        }

        public Expr Ge(Expr lhs, Expr rhs)
        {
            if (!lhs.Type.Equals(rhs.Type))
            {
                throw new ExprTypeCheckException("lhs and rhs must be the same type");
            }

            if (!lhs.Type.IsInt && !lhs.Type.IsReal)
            {
                throw new ExprTypeCheckException("lhs and rhs must both be of int type or real type");
            }
            var result = GetNAry(GetBinaryFunction(BinaryOperator.Opcode.Ge), new List<Expr>() { lhs, rhs });
            result.Type = BasicType.Bool;
            return result;
        }

        private ConcurrentDictionary<ArithmeticCoercion.CoercionType, ArithmeticCoercion> ArithmeticCoercionCache = new ConcurrentDictionary<ArithmeticCoercion.CoercionType, ArithmeticCoercion>();
        public Expr ArithmeticCoercion(ArithmeticCoercion.CoercionType coercionType, Expr operand)
        {
            Microsoft.Boogie.Type resultType = null;
            switch (coercionType)
            {
                case Microsoft.Boogie.ArithmeticCoercion.CoercionType.ToInt:
                    if (!operand.Type.IsReal)
                        throw new ExprTypeCheckException("When coercising to int operand must be a real");

                    resultType = BasicType.Int;
                    break;
                case Microsoft.Boogie.ArithmeticCoercion.CoercionType.ToReal:
                    if (!operand.Type.IsInt)
                        throw new ExprTypeCheckException("When coercising to real operand must be an int");

                    resultType = BasicType.Real;
                    break;
                default:
                    throw new ArgumentException("coercionType not supported");
            }

            // Use Cache
            ArithmeticCoercion coercionFun = null;
            try
            {
                coercionFun = ArithmeticCoercionCache[coercionType];
            }
            catch (KeyNotFoundException)
            {
                coercionFun = new ArithmeticCoercion(Token.NoToken, coercionType);
                ArithmeticCoercionCache[coercionType] = coercionFun;
            }

            var result = GetNAry(coercionFun, new List<Expr>() { operand });
            result.Type = resultType;
            return result;
        }

        private ConcurrentDictionary<int, MapSelect> MapSelectCache = new ConcurrentDictionary<int, Microsoft.Boogie.MapSelect>();
        public Expr MapSelect(Expr map, params Expr[] indices)
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

            // Use Cache
            MapSelect ms = null;
            try
            {
                ms = MapSelectCache[indices.Length];
            }
            catch (KeyNotFoundException)
            {
                ms = new MapSelect(Token.NoToken, indices.Length);
                MapSelectCache[indices.Length] = ms;
            }

            var argList = new List<Expr>() { map };
            for (int index = 0; index < indices.Length; ++index)
            {
                argList.Add(indices[index]);
            }

            // Type check each argument
            foreach (var typePair in map.Type.AsMap.Arguments.Zip(indices.Select( i => i.ShallowType)))
            {
                if (!typePair.Item1.Equals(typePair.Item2))
                {
                    throw new ExprTypeCheckException("Map argument type mismatch. " + typePair.Item1.ToString() + " != " + typePair.Item2.ToString());
                }
            }

            var result = GetNAry(ms, argList);
            result.Type = map.Type.AsMap.Result;
            return result;
        }

        private ConcurrentDictionary<int, MapStore> MapStoreCache = new ConcurrentDictionary<int, MapStore>();
        public Expr MapStore(Expr map, Expr value, params Expr[] indices)
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

            if (!map.Type.AsMap.Result.Equals(value.Type))
            {
                throw new ExprTypeCheckException("value (" + value.Type.ToString() + ") must match map's result type (" + map.Type.AsMap.Result.ToString() + ")");
            }

            // Use Cache
            MapStore ms = null;
            try
            {
                ms = MapStoreCache[indices.Length];
            }
            catch (KeyNotFoundException)
            {
                ms = new MapStore(Token.NoToken, indices.Length);
                MapStoreCache[indices.Length] = ms;
            }


            // Type check each argument
            foreach (var typePair in map.Type.AsMap.Arguments.Zip(indices.Select( i => i.ShallowType)))
            {
                if (!typePair.Item1.Equals(typePair.Item2))
                {
                    throw new ExprTypeCheckException("Map argument type mismatch. " + typePair.Item1.ToString() + " != " + typePair.Item2.ToString());
                }
            }

            // Build the argument list
            var argList = new List<Expr>() { map }; // First argument is map to add store to
            for (int index = 0; index < indices.Length; ++index)
            {
                argList.Add(indices[index]);
            }

            // Now add the last argument which is the value to store
            argList.Add(value);


            var result = GetNAry(ms, argList);
            result.Type = map.Type;
            return result;
        }

        public Expr Old(Expr operand)
        {
            var result = new OldExpr(Token.NoToken, operand, Immutable);
            result.Type = operand.Type;
            return result;
        }

        public Expr ForAll(IList<Variable> freeVars, Expr body, Trigger triggers=null)
        {
            if (!body.Type.IsBool)
            {
                throw new ExprTypeCheckException("body must be of type bool");
            }

            if (freeVars.Count < 1)
            {
                throw new ArgumentException("ForAllExpr must have at least one free variable");
            }

            TypeCheckTriggers(freeVars, body, triggers);

            // Should we check the free variables are actually used? This could be quite expensive to do!
            var result = new ForallExpr(Token.NoToken, new List<Variable>(freeVars), triggers, body, Immutable);
            result.Type = BasicType.Bool;
            return result;
        }

        public Expr Exists(IList<Variable> freeVars, Expr body, Trigger triggers=null)
        {
            if (!body.Type.IsBool)
            {
                throw new ExprTypeCheckException("body must be of type bool");
            }

            if (freeVars.Count < 1)
            {
                throw new ArgumentException("ExistsExpr must have at least one free variable");
            }

            TypeCheckTriggers(freeVars, body, triggers);

            // Should we check the free variables are actually used? This could be quite expensive to do!
            var result = new ExistsExpr(Token.NoToken, new List<Variable>(freeVars), triggers, body, Immutable);
            result.Type = BasicType.Bool;
            return result;
        }

        private void TypeCheckTriggers(IList<Variable> freeVars, Expr body, Trigger triggers)
        {
            // TODO:
        }

        public Expr Distinct(IList<Expr> exprs)
        {
            if (exprs.Count < 1)
                throw new ArgumentException("Distinct must have at least two arguments");

            // Check the types
            var firstType = exprs[0].Type;

            if (firstType == null)
                throw new ExprTypeCheckException("First argument cannot have a null Type");

            for (int index = 1; index < exprs.Count; ++index)
            {
                if (!firstType.Equals(exprs[index].Type))
                    throw new ExprTypeCheckException(String.Format("The first argument and expr type at index (zero indexded) {0} do not match", index));
            }

            var distinctOp = new DistinctOperator(Token.NoToken, exprs.Count);
            var result = new NAryExpr(Token.NoToken, distinctOp, exprs, Immutable);
            result.Type = BasicType.Bool;
            return result;
        }
    }
}
