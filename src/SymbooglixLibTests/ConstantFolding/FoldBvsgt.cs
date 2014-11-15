using NUnit.Framework;
using System;
using Symbooglix;
using Microsoft.Boogie;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBvsgt : TestBase
    {
        [Test()]
        public void PositivePositiveTrue()
        {
            helper(6, 5, true);
        }

        [Test()]
        public void PositivePositiveFalseEqual()
        {
            helper(6, 6, false);
        }

        [Test()]
        public void PositivePositiveFalse()
        {
            helper(5, 6, false);
        }

        [Test()]
        public void PositiveNegativeTrue()
        {
            helper(6, -5, true);
        }

        [Test()]
        public void NegativePositiveFalse()
        {
            helper(-6, 5, false);
        }

        [Test()]
        public void NegativeNegativeTrue()
        {
            helper(-5, -6, true);
        }

        [Test()]
        public void NegativeNegativeFalse()
        {
            helper(-6, -5, false);
        }

        [Test()]
        public void NegativeNegativeFalseEqual()
        {
            helper(-6, -6, false);
        }



        private void helper(int value0, int value1, bool truth)
        {
            var x = builder.ConstantBV(value0, 4);
            var y = builder.ConstantBV(value1, 4);
            var bvslt = builder.BVSGT(x, y);

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(bvslt);

            Assert.IsInstanceOf<LiteralExpr>(result);
            Assert.IsTrue(( result as LiteralExpr ).isBool);
            Assert.IsTrue(( result as LiteralExpr ).asBool == truth);
        }
    }
}

