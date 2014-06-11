using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.IO;
using symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Literal
    {
        public Literal()
        {
            SymbooglixTest.setupDebug();
        }

        [Test()]
        public void bitvector()
        {
            var literal = new LiteralExpr(Token.NoToken, BigNum.FromInt(19), 32); // 19bv32
            checkLiteral(literal, "(_ bv19 32)");
        }

        [Test()]
        public void Bools()
        {
            checkLiteral(Expr.True, "true");
            checkLiteral(Expr.False, "false");
        }

        private void checkLiteral(LiteralExpr e, string expected)
        {
            using (var writer = new StringWriter())
            {
                var printer = new SMTLIBQueryPrinter(writer);
                printer.Traverse(e);
                Assert.IsTrue(writer.ToString() == expected);
            }
        }
    }
}

