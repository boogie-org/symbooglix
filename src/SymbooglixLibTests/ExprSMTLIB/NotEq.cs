//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2017 Daniel Liew
//
// This file is licensed under the MIT license.
// See LICENSE.txt for details.
//------------------------------------------------------------------------------
using System;
using Symbooglix.Solver;
using Symbooglix;
using System.IO;
using NUnit.Framework;

namespace ExprSMTLIBTest
{
    [TestFixture()]
    public class NotEq : ExprSMTLIBTestBase
    {
        [Test()]
        public void Test()
        {
            var builder = new SimpleExprBuilder(/*immutable=*/ true);
            var bv0_32 = builder.ConstantBV(0,32);
            var bv1_32 = builder.ConstantBV(1, 32);
            var neq = builder.NotEq(bv0_32, bv1_32);

            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.PrintExpr(neq);
                Assert.AreEqual("(distinct (_ bv0 32) (_ bv1 32) )", writer.ToString());
            }

        }
    }
}

