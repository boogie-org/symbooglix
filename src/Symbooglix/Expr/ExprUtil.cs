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
using System.Diagnostics;
using System.Numerics;

namespace Symbooglix
{
    public class ExprUtil
    {
        public static LiteralExpr AsLiteral(Expr e)
        {
            return e as LiteralExpr;
        }

        public static IdentifierExpr AsIdentifer(Expr e)
        {
            return e as IdentifierExpr;
        }

        public static SymbolicVariable AsSymbolicVariable(Expr e)
        {
            var asId = AsIdentifer(e);
            if (asId == null)
                return null;

            if (asId.Decl is SymbolicVariable)
            {
                return asId.Decl as SymbolicVariable;
            }
            else
                return null;
        }

        public static bool IsTrue(Expr e)
        {
            var lit = AsLiteral(e);
            if (lit != null)
            {
                return lit.IsTrue;
            }
            return false;
        }

        public static bool IsFalse(Expr e)
        {
            var lit = AsLiteral(e);
            if (lit != null)
            {
                return lit.IsFalse;
            }
            return false;
        }

        public static NAryExpr AsIfThenElse(Expr e)
        {
            return InternalAsFun<IfThenElse>(e);
        }

        public static bool StructurallyEqual(Expr a, Expr b)
        {
            Debug.Assert(a.Immutable);
            Debug.Assert(b.Immutable);
            if (Object.ReferenceEquals(a, b))
                return true;

            // Do quick check first
            if (a.GetHashCode() != b.GetHashCode())
                return false;

            // Same hashcodes but the Expr could still be structurally different
            // so compute by traversing (much slower)
            return a.Equals(b);
        }

        public static NAryExpr AsNot(Expr e)
        {
            return GetUnaryOperator(e, UnaryOperator.Opcode.Not);
        }

        public static NAryExpr AsNotEq(Expr e)
        {
            return GetBinaryOperator(e, BinaryOperator.Opcode.Neq);
        }

        public static NAryExpr AsEq(Expr e)
        {
            return GetBinaryOperator(e, BinaryOperator.Opcode.Eq);
        }

        public static NAryExpr AsNeg(Expr e)
        {
            return GetUnaryOperator(e, UnaryOperator.Opcode.Neg);
        }

        public static NAryExpr AsGt(Expr e)
        {
            return GetBinaryOperator(e, BinaryOperator.Opcode.Gt);
        }

        public static NAryExpr AsGe(Expr e)
        {
            return GetBinaryOperator(e, BinaryOperator.Opcode.Ge);
        }

        public static NAryExpr AsLt(Expr e)
        {
            return GetBinaryOperator(e, BinaryOperator.Opcode.Lt);
        }

        public static NAryExpr AsLe(Expr e)
        {
            return GetBinaryOperator(e, BinaryOperator.Opcode.Le);
        }

        private static NAryExpr GetUnaryOperator(Expr e, UnaryOperator.Opcode opcode)
        {
            var nary = e as NAryExpr;
            if (nary == null)
                return null;

            var fun = nary.Fun;
            if (fun is UnaryOperator)
            {
                var unary = fun as UnaryOperator;
                if (unary.Op == opcode)
                    return nary;
            }
            return null;
        }

        private static NAryExpr GetBinaryOperator(Expr e, BinaryOperator.Opcode opcode)
        {
            var nary = e as NAryExpr;
            if (nary == null)
                return null;

            var fun = nary.Fun;
            if (fun is BinaryOperator)
            {
                var binary = fun as BinaryOperator;
                if (binary.Op == opcode)
                    return nary;
            }
            return null;
        }

        public static NAryExpr AsDiv(Expr e)
        {
            return GetBinaryOperator(e, BinaryOperator.Opcode.Div);
        }

        public static NAryExpr AsMod(Expr e)
        {
            return GetBinaryOperator(e, BinaryOperator.Opcode.Mod);
        }

        public static NAryExpr AsImp(Expr e)
        {
            return GetBinaryOperator(e, BinaryOperator.Opcode.Imp);
        }

        public static NAryExpr AsAdd(Expr e)
        {
            return GetBinaryOperator(e, BinaryOperator.Opcode.Add);
        }

        public static NAryExpr AsMul(Expr e)
        {
            return GetBinaryOperator(e, BinaryOperator.Opcode.Mul);
        }

        private static NAryExpr GetBVOperator(Expr e, string builtin)
        {
            var nary = e as NAryExpr;
            if (nary == null)
                return null;
            var fc = nary.Fun as FunctionCall;
            if (fc == null)
                return null;

            var usedBuiltin = fc.Func.FindStringAttribute("bvbuiltin");
            if (usedBuiltin == null)
                return null;

            if (usedBuiltin == builtin)
                return nary;
            else
                return null;
        }

        public static NAryExpr AsBVADD(Expr e)
        {
            return GetBVOperator(e, "bvadd");
        }

        public static NAryExpr AsBVSUB(Expr e)
        {
            return GetBVOperator(e, "bvsub");
        }

        public static NAryExpr AsBVMUL(Expr e)
        {
            return GetBVOperator(e, "bvmul");
        }

        public static NAryExpr AsBVUDIV(Expr e)
        {
            return GetBVOperator(e, "bvudiv");
        }

        public static NAryExpr AsBVUREM(Expr e)
        {
            return GetBVOperator(e, "bvurem");
        }

        public static NAryExpr AsBVSDIV(Expr e)
        {
            return GetBVOperator(e, "bvsdiv");
        }

        public static NAryExpr AsBVSREM(Expr e)
        {
            return GetBVOperator(e, "bvsrem");
        }

        public static NAryExpr AsBVSMOD(Expr e)
        {
            return GetBVOperator(e, "bvsmod");
        }

        public static NAryExpr AsBVNEG(Expr e)
        {
            return GetBVOperator(e, "bvneg");
        }

        public static NAryExpr AsBVNOT(Expr e)
        {
            return GetBVOperator(e, "bvnot");
        }

        public static NAryExpr AsBVSEXT(Expr e)
        {
            var nary = e as NAryExpr;
            if (nary == null)
                return null;
            var fc = nary.Fun as FunctionCall;
            if (fc == null)
                return null;

            var usedBuiltin = fc.Func.FindStringAttribute("bvbuiltin");

            if (usedBuiltin == null)
                return null;

            var regex = new System.Text.RegularExpressions.Regex("^sign_extend \\d+$");

            if (regex.IsMatch(usedBuiltin))
            {
                return nary;
            }

            return null;
        }

        public static NAryExpr AsBVZEXT(Expr e)
        {
            var nary = e as NAryExpr;
            if (nary == null)
                return null;
            var fc = nary.Fun as FunctionCall;
            if (fc == null)
                return null;

            var usedBuiltin = fc.Func.FindStringAttribute("bvbuiltin");

            if (usedBuiltin == null)
                return null;

            var regex = new System.Text.RegularExpressions.Regex("^zero_extend \\d+$");

            if (regex.IsMatch(usedBuiltin))
            {
                return nary;
            }

            return null;
        }

        public static BvConcatExpr AsBVCONCAT(Expr e)
        {
            return e as BvConcatExpr;
        }

        public static BvExtractExpr AsBVEXTRACT(Expr e)
        {
            return e as BvExtractExpr;
        }

        public static NAryExpr AsBVSLT(Expr e)
        {
            return GetBVOperator(e, "bvslt");
        }

        public static NAryExpr AsBVSLE(Expr e)
        {
            return GetBVOperator(e, "bvsle");
        }

        public static NAryExpr AsBVSGT(Expr e)
        {
            return GetBVOperator(e, "bvsgt");
        }

        public static NAryExpr AsBVSGE(Expr e)
        {
            return GetBVOperator(e, "bvsge");
        }

        public static NAryExpr AsBVULT(Expr e)
        {
            return GetBVOperator(e, "bvult");
        }

        public static NAryExpr AsBVULE(Expr e)
        {
            return GetBVOperator(e, "bvule");
        }

        public static NAryExpr AsBVUGT(Expr e)
        {
            return GetBVOperator(e, "bvugt");
        }

        public static NAryExpr AsBVUGE(Expr e)
        {
            return GetBVOperator(e, "bvuge");
        }

        public static NAryExpr AsBVAND(Expr e)
        {
            return GetBVOperator(e, "bvand");
        }

        public static NAryExpr AsBVOR(Expr e)
        {
            return GetBVOperator(e, "bvor");
        }

        public static NAryExpr AsBVXOR(Expr e)
        {
            return GetBVOperator(e, "bvxor");
        }

        public static NAryExpr AsBVSHL(Expr e)
        {
            return GetBVOperator(e, "bvshl");
        }

        public static NAryExpr AsBVLSHR(Expr e)
        {
            return GetBVOperator(e, "bvlshr");
        }

        public static NAryExpr AsBVASHR(Expr e)
        {
            return GetBVOperator(e, "bvashr");
        }

        private static NAryExpr InternalAsFun<T>(Expr e)
        {
            var asNary = e as NAryExpr;
            if (asNary == null)
                return null;

            var fun = asNary.Fun;
            if (fun is T)
                return asNary;

            return null;
        }

        public static NAryExpr AsUninterpretedFunctionCall(Expr e) {
            var asFunctionCall = InternalAsFun<FunctionCall>(e);
            if (asFunctionCall == null)
                return null;

            var function = ( asFunctionCall.Fun as FunctionCall ).Func;

            var asUF = AsUninterpretedFunction(function);
            if (asUF == null)
                return null;

            return asFunctionCall;
        }

        public static Function AsUninterpretedFunction(Function f)
        {
            // FIXME: Should we maintain a list of known built-ins and check against that?
            var bvBuiltin = f.FindStringAttribute("bvbuiltin");
            if (bvBuiltin != null)
                return null;

            // Check if its a builtin
            var builtin = f.FindStringAttribute("builtin");
            if (builtin != null)
                return null;

            return f;
        }

        public static NAryExpr AsArithmeticCoercion(Expr e)
        {
            return InternalAsFun<ArithmeticCoercion>(e);
        }

        public static NAryExpr AsMapSelect(Expr e)
        {
            return InternalAsFun<MapSelect>(e);
        }

        public static NAryExpr AsMapStore(Expr e)
        {
            return InternalAsFun<MapStore>(e);
        }

        public static bool IsZero(Expr e)
        {
            var lit = AsLiteral(e);
            if (lit == null)
                return false;

            if (lit.isBvConst)
            {
                return lit.asBvConst.Value.IsZero;
            }
            else if (lit.isBigNum)
            {
                return lit.asBigNum.IsZero;
            }
            else if (lit.isBigDec)
            {
                return lit.asBigDec.IsZero;
            }

            return false;
        }

        public static bool IsOne(Expr e)
        {
            var lit = AsLiteral(e);
            if (lit == null)
                return false;

            if (lit.isBvConst)
            {
                return lit.asBvConst.Value.ToBigInteger.IsOne;
            }
            else if (lit.isBigNum)
            {
                return lit.asBigNum.ToBigInteger.IsOne;
            }
            else if (lit.isBigDec)
            {
                return lit.asBigDec.Equals(Microsoft.Basetypes.BigDec.FromInt(1));
            }

            return false;
        }

        public static bool IsBVAllOnes(Expr e)
        {
            var asLit = AsLiteral(e);
            if (asLit == null)
                return false;

            if (!asLit.isBvConst)
                return false;

            var AllOnesValue = ( System.Numerics.BigInteger.One << asLit.asBvConst.Bits ) - 1;
            return asLit.asBvConst.Value.ToBigInteger == AllOnesValue;
        }
    }
}

