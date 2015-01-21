using NUnit.Framework;
using System;
using Symbooglix;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.IO;

namespace ExprSMTLIBTest
{
    [TestFixture()]
    public class UninterpretedFunction
    {
        public UninterpretedFunction()
        {
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
            Builder = new SimpleExprBuilder();
        }

        private SimpleExprBuilder Builder;
        [Test()]
        public void TestCase()
        {
            Builder = new SimpleExprBuilder();

            var functionCall = Builder.CreateUninterpretedFunctionCall("uf", Microsoft.Boogie.Type.Bool, new List<Microsoft.Boogie.Type>() {
                Microsoft.Boogie.Type.Int,
                Microsoft.Boogie.Type.Real
            });

            // FIXME: Perhaps this should be moved into the ExprBuilder
            var e = new NAryExpr(Token.NoToken, functionCall, new List<Expr>() {
                Builder.ConstantInt(5),
                Builder.ConstantReal("5.5")
            });

            // FIXME: This needs to be factored out
            using (var writer = new StringWriter())
            {
                var printer = new SMTLIBQueryPrinter(writer, false, false);
                printer.AddDeclarations(e);
                printer.PrintFunctionDeclarations();
                printer.PrintExpr(e);
                Assert.AreEqual("(declare-fun uf (Int Real ) Bool)" + Environment.NewLine + "(uf 5 5.5  )", writer.ToString());
            }
        }
    }
}

