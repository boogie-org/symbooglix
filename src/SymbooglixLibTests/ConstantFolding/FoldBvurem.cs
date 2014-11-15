using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Symbooglix;
using Microsoft.Basetypes;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBvurem : TestBase
    {
        [Test()]
        public void NoRemainder()
        {
            var arg0 = builder.ConstantBV(4, 4);
            var arg1 = builder.ConstantBV(2, 4);
            helper(arg0, arg1,0);
        }

        [Test()]
        public void WithRemainder()
        {
            var arg0 = builder.ConstantBV(7, 4);
            var arg1 = builder.ConstantBV(5, 4);
            helper(arg0, arg1,2);
        }

        [Test(),ExpectedException(typeof(DivideByZeroException))]
        public void DivisionByZero()
        {
            var arg0 = builder.ConstantBV(7, 4);
            var arg1 = builder.ConstantBV(0, 4);
            helper(arg0, arg1,0);
        }

        private Expr helper(Expr arg0, Expr arg1, int expectedValue)
        {
            var urem = builder.BVUREM(arg0, arg1);

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(urem);
            // FIXME: Refactor this stuff into TestBase
            Assert.IsInstanceOf<LiteralExpr>(result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(BigNum.FromInt(expectedValue), ( result as LiteralExpr ).asBvConst.Value);
            return result;
        }
    }
}

