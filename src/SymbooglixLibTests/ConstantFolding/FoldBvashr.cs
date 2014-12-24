using NUnit.Framework;
using System;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBvashr : TestBase
    {
        [Test()]
        public void MSBIsZero()
        {
            helper(5, 2, 1);
        }

        [Test()]
        public void MSBIsOne()
        {
            helper(12, 2, 15);
        }

        [Test()]
        public void ShiftWidthOutOfRange()
        {
            helper(15, 4, 0);
        }

        private void helper(int arg0, int arg1, int expectedResult)
        {
            var valueToShift = builder.ConstantBV(arg0, 4);
            var shiftWidth = builder.ConstantBV(arg1, 4);
            var expr = builder.BVASHR(valueToShift, shiftWidth);
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(expr);

            Assert.IsInstanceOf<LiteralExpr>(result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(BigNum.FromInt(expectedResult), ( result as LiteralExpr ).asBvConst.Value);
        }
    }
}

