using System;
using Microsoft.Boogie;

namespace Symbooglix
{
    public class ExprUtil
    {
        public static LiteralExpr AsLiteral(Expr e)
        {
            return e as LiteralExpr;
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
    }
}

