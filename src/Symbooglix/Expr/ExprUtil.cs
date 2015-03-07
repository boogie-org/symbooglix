using System;
using Microsoft.Boogie;
using System.Diagnostics;

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
            var narry = e as NAryExpr;
            if (narry == null)
                return null;

            var fun = narry.Fun;
            if (fun is IfThenElse)
                return narry;
            else
                return null;
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

        public static NAryExpr AsNeg(Expr e)
        {
            return GetUnaryOperator(e, UnaryOperator.Opcode.Neg);
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

        public static NAryExpr AsBVMUL(Expr e)
        {
            return GetBVOperator(e, "bvmul");
        }

        public static NAryExpr AsBVUGT(Expr e)
        {
            return GetBVOperator(e, "bvugt");
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
    }
}

