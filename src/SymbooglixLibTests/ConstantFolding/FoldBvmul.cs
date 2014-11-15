using NUnit.Framework;
using System;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBvmul : TestBase
    {
        [Test()]
        public void PositiveNoOverflow()
        {
            var arg0 = builder.ConstantBV(5, 4);
            var arg1 = builder.ConstantBV(2, 4);
            helper(arg0, arg1, 10);
        }

        [Test()]
        public void PositiveOverflow()
        {
            var arg0 = builder.ConstantBV(5, 4);
            var arg1 = builder.ConstantBV(5, 4);
            helper(arg0, arg1, 9);
        }

        [Test()]
        public void NegativeNoUnderflow()
        {
            var arg0 = builder.ConstantBV(-2, 4);
            var arg1 = builder.ConstantBV(3, 4);

            // There is actually overflow happening here but if we
            // consider the bitvectors as two's complement then no
            // overflow occured
            var result = helper(arg0, arg1, 10);
            Assert.IsTrue(result.Equals(builder.ConstantBV(-6,4)));
        }

        [Test()]
        public void NegativeUnderflow()
        {
            var arg0 = builder.ConstantBV(-2, 4);
            var arg1 = builder.ConstantBV(5, 4);
            helper(arg0, arg1, 6);

        }

        private Expr helper(Expr arg0, Expr arg1, int expectedValue)
        {
            var mul = builder.BVMUL(arg0, arg1);

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(mul);
            Assert.IsInstanceOf<LiteralExpr>(result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(BigNum.FromInt(expectedValue), ( result as LiteralExpr ).asBvConst.Value);
            return result;
        }
    }
}

