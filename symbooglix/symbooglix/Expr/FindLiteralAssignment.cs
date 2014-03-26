using Microsoft.Boogie;
using System;
using System.Diagnostics;
using System.Linq;

namespace symbooglix
{
    public class FindLiteralAssignment
    {
        public static bool find(Expr root, Variable v, out LiteralExpr literal)
        {
            Variable found = null;
            findAnyVariable(root, out found, out literal);

            if (found == v)
            {
                Debug.Assert(literal != null);
                return true;
            }
            else
            {
                literal = null;
                return false;
            }
        }

        public static bool findAnyVariable(Expr root, out Variable v, out LiteralExpr literal)
        {
            if (root is NAryExpr)
            {
                var naryExpr = root as NAryExpr;
                var idExpr = naryExpr.Args.OfType<IdentifierExpr>();
                if (idExpr.Count() == 0)
                {
                    v = null;
                    literal = null;
                    return false;
                }

                if (naryExpr.Fun is BinaryOperator && ( naryExpr.Fun as BinaryOperator ).Op == BinaryOperator.Opcode.Eq)
                {
                    Debug.Assert(idExpr.Count() == 1, "Found more than one Identifier expression");

                    var literalExpr = naryExpr.Args.OfType<LiteralExpr>();
                    if (literalExpr.Count() > 0)
                    {
                        v = idExpr.First().Decl;
                        literal = literalExpr.First();
                        return true;
                    }
                }

            }

            v = null;
            literal = null;
            return false;

        }
    }
}