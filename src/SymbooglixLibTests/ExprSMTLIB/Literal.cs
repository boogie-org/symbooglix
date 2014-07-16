using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.IO;
using Symbooglix;

namespace ExprSMTLIBTest
{
    [TestFixture()]
    public class Literal
    {
        public Literal()
        {
            SymbooglixLibTests.SymbooglixTest.setupDebug();
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

        [Test()]
        public void Reals()
        {
            // FIXME: We shouldn't be using helpers in other test suites, instead the helper
            // should be moved into Symbooglix somewhere
            var literal = ConstantFoldingTests.TestBase.getConstantReal("-1.5e0");
            checkLiteral(literal, "-1.5");
        }

        [Test()]
        public void Integers()
        {
            // FIXME: We shouldn't be using helpers in other test suites, instead the helper
            // should be moved into Symbooglix somewhere
            var literal = ConstantFoldingTests.TestBase.getConstantInt(-15);
            checkLiteral(literal, "-15");
        }

        private void checkLiteral(LiteralExpr e, string expected)
        {
            using (var writer = new StringWriter())
            {
                var printer = new SMTLIBQueryPrinter(writer);
                printer.PrintExpr(e);
                Assert.IsTrue(writer.ToString() == expected);
            }
        }
    }
}

