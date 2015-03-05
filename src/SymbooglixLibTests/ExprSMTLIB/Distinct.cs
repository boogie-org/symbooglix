﻿using System;
using NUnit.Framework;
using System.Collections.Generic;
using Symbooglix;
using System.IO;
using Microsoft.Boogie;

namespace ExprSMTLIBTest
{
    [TestFixture()]
    public class Distinct
    {
        [Test()]
        public void Test()
        {
            var builder = new SimpleExprBuilder(/*immutable=*/true);
            var v0 = builder.False;
            var v1 = builder.True;
            var distinct = builder.Distinct(new List<Expr>() { v0, v1 });

            using (var writer = new StringWriter())
            {
                var printer = new SMTLIBQueryPrinter(writer, false, false);
                printer.PrintExpr(distinct);
                Assert.AreEqual("(distinct false true )", writer.ToString());
            }
        }
    }
}

