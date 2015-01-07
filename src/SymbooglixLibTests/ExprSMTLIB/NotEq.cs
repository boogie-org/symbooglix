using System;
using Symbooglix.Solver;
using Symbooglix;
using System.IO;
using NUnit.Framework;

namespace ExprSMTLIBTest
{
    [TestFixture()]
    public class NotEq
    {
        [Test()]
        public void Test()
        {
            var builder = new SimpleExprBuilder();
            var bv0_32 = builder.ConstantBV(0,32);
            var bv1_32 = builder.ConstantBV(1, 32);
            var neq = builder.NotEq(bv0_32, bv1_32);

            using (var writer = new StringWriter())
            {
                var printer = new SMTLIBQueryPrinter(writer, false, false);
                printer.PrintExpr(neq);
                Assert.AreEqual("(not (= (_ bv0 32) (_ bv1 32) ) )", writer.ToString());
            }

        }
    }
}

