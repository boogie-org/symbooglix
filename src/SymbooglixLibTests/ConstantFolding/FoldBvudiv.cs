using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Symbooglix;
using Microsoft.Basetypes;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBvudiv : TestBase
    {
        [Test()]
        public void NoTruncation()
        {
            var arg0 = builder.ConstantBV(8, 4);
            var arg1 = builder.ConstantBV(2, 4);
            helper(arg0, arg1, 4);
        }

        [Test()]
        public void Truncation()
        {
            var arg0 = builder.ConstantBV(7, 4);
            var arg1 = builder.ConstantBV(3, 4);
            helper(arg0, arg1, 2);
        }

        [Test(),ExpectedException(typeof(DivideByZeroException))]
        public void DivionByZero()
        {
            var arg0 = builder.ConstantBV(7, 4);
            var arg1 = builder.ConstantBV(0, 4);
            helper(arg0, arg1, 0);
        }


        private Expr helper(Expr arg0, Expr arg1, int expectedValue)
        {
            var udiv = builder.BVUDIV(arg0, arg1);

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(udiv);
            Assert.IsInstanceOf<LiteralExpr>(result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(BigNum.FromInt(expectedValue), ( result as LiteralExpr ).asBvConst.Value);
            return result;
        }
    }
}

