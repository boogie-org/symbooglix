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
using Symbooglix.Solver;
using Symbooglix;
using System.IO;
using NUnit.Framework;

namespace ExprSMTLIBTest
{
    [TestFixture()]
    public class Iff
    {
        [Test()]
        public void Test()
        {
            var builder = new SimpleExprBuilder(/*immutable=*/true);
            var boolTrue = builder.ConstantBool(true);
            var boolFalse = builder.ConstantBool(false);
            var iffExpr = builder.Iff(boolTrue, boolFalse);

            using (var writer = new StringWriter())
            {
                var printer = new SMTLIBQueryPrinter(writer, false, false);
                printer.PrintExpr(iffExpr);
                Assert.AreEqual("(and (=> true false ) (=> false true ) )", writer.ToString());
            }

        }
    }
}

