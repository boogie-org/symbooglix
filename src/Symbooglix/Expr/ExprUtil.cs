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
            var nary = e as NAryExpr;
            if (nary == null)
                return null;

            var fun = nary.Fun;
            if (fun is UnaryOperator)
            {
                var unary = fun as UnaryOperator;
                if (unary.Op == UnaryOperator.Opcode.Not)
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
    }
}

