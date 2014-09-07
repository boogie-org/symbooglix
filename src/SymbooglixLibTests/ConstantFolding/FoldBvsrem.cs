using NUnit.Framework;
using System;
using Symbooglix;
using Microsoft.Boogie;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBvsrem : TestBase
    {
        [Test()]
        public void PositiveNumeratorPositiveDenominatorWithRemainder()
        {
            var arg0 = builder.ConstantBV(7, 4);
            var arg1 = builder.ConstantBV(2, 4);
            helper(arg0, arg1, 1);
        }

        [Test()]
        public void PositiveNumeratorPositiveDenominatorNoRemainder()
        {
            var arg0 = builder.ConstantBV(8, 4);
            var arg1 = builder.ConstantBV(2, 4);
            helper(arg0, arg1, 0);
        }

        [Test()]
        public void PositiveNumeratorNegativeDenominatorWithRemainder()
        {
            var arg0 = builder.ConstantBV(7, 4);
            var arg1 = builder.ConstantBV(-2, 4);
            helper(arg0, arg1, 1);
        }

        [Test()]
        public void PositiveNumeratorNegativeDenominatorNoRemainder()
        {
            var arg0 = builder.ConstantBV(8, 4);
            var arg1 = builder.ConstantBV(-2, 4);
            helper(arg0, arg1, 0);
        }

        [Test()]
        public void NegativeNumeratorPositiveDenominatorWithRemainder()
        {
            var arg0 = builder.ConstantBV(-7, 4);
            var arg1 = builder.ConstantBV(2, 4);
            helper(arg0, arg1, -1);
        }

        [Test()]
        public void NegativeNumeratorNegativeDenominatorWithRemainder()
        {
            var arg0 = builder.ConstantBV(-7, 4);
            var arg1 = builder.ConstantBV(-2, 4);
            helper(arg0, arg1, 1);
        }

        [Test(),ExpectedException(typeof(DivideByZeroException))]
        public void DivisionByZero()
        {
            var arg0 = builder.ConstantBV(-7, 4);
            var arg1 = builder.ConstantBV(0, 4);
            helper(arg0, arg1, 0);
        }

        private Expr helper(Expr arg0, Expr arg1, int expected)
        {
            var srem = builder.BVSREM(arg0, arg1);

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(srem);
            Assert.IsInstanceOfType(typeof(LiteralExpr), result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(builder.ConstantBV(expected, 4).asBvConst.Value, ( result as LiteralExpr ).asBvConst.Value);
            return result;
        }
    }
}

