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
using Symbooglix;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.IO;

namespace ExprSMTLIBTest
{
    [TestFixture()]
    public class UninterpretedFunction : ExprSMTLIBTestBase
    {
        public UninterpretedFunction()
        {
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
            SEB = new SimpleExprBuilder(/*immutable=*/ true);
        }

        private SimpleExprBuilder SEB;
        [Test()]
        public void TestCase()
        {
            var FCB = new FunctionCallBuilder();

            var functionCall = FCB.CreateUninterpretedFunctionCall("uf", Microsoft.Boogie.Type.Bool, new List<Microsoft.Boogie.Type>() {
                Microsoft.Boogie.Type.Int,
                Microsoft.Boogie.Type.Real
            });


            var e = SEB.UFC(functionCall, SEB.ConstantInt(5), SEB.ConstantReal("5.5"));

            // FIXME: This needs to be factored out
            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.AddDeclarations(e);
                printer.PrintFunctionDeclarations();
                printer.PrintExpr(e);
                Assert.AreEqual("(declare-fun uf (Int Real ) Bool)" + Environment.NewLine + "(uf 5 5.5  )", writer.ToString());
            }
        }
    }
}

