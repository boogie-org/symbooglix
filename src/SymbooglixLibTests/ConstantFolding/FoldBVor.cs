using NUnit.Framework;
using System;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBVor : TestBase
    {
        [Test()]
        public void AllOnes()
        {
            helper(5, 10, 15);
        }

        [Test()]
        public void SomeOnes()
        {
            helper(1, 2, 3);
        }

        [Test()]
        public void Ends()
        {
            helper(1, 8, 9);
        }

        private void helper(int value0, int value1, int expectedValue)
        {
            var simple = builder.ConstantBV(value0, 4);
            var simple2 = builder.ConstantBV(value1, 4);
            var expr = builder.BVOR(simple, simple2);
            expr.Typecheck(new TypecheckingContext(this));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(expr);

            Assert.IsInstanceOfType(typeof(LiteralExpr), result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(BigNum.FromInt(expectedValue), ( result as LiteralExpr ).asBvConst.Value);
        }
    }
}

