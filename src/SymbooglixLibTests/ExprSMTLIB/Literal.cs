//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.IO;
using Symbooglix;

namespace ExprSMTLIBTest
{
    [TestFixture()]
    public class Literal : ExprSMTLIBTestBase
    {
        IExprBuilder Builder;
        public Literal()
        {
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
            Builder = new SimpleExprBuilder(/*immutable=*/ true);
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
            var literal = Builder.ConstantReal("-1.5e0");
            checkLiteral(literal, "-1.5");
        }

        [Test()]
        public void Integers()
        {
            var literal = Builder.ConstantInt(-15);
            checkLiteral(literal, "-15");
        }

        private void checkLiteral(LiteralExpr e, string expected)
        {
            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.PrintExpr(e);
                Assert.IsTrue(writer.ToString() == expected);
            }
        }
    }
}

