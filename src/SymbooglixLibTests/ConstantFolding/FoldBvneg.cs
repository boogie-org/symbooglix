using NUnit.Framework;
using System;
using System.Numerics;
using Symbooglix;
using Microsoft.Boogie;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBvneg : TestBase
    {
        [Test()]
        public void Positive()
        {
            var arg0 = builder.ConstantBV(7, 4);

            var neg = builder.BVNEG(arg0);
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(neg);
            Assert.IsInstanceOf<LiteralExpr>(result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(new BigInteger(9), ( result as LiteralExpr ).asBvConst.Value.ToBigInteger);
            Assert.IsTrue(builder.ConstantBV(-7, 4).Equals(result));
        }

        [Test()]
        public void Negative()
        {
            var arg0 = builder.ConstantBV(-5, 4);

            var neg = builder.BVNEG(arg0);
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(neg);
            Assert.IsInstanceOf<LiteralExpr>(result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(new BigInteger(5), ( result as LiteralExpr ).asBvConst.Value.ToBigInteger);
            Assert.IsTrue(builder.ConstantBV(5, 4).Equals(result));
        }

        [Test()]
        public void Zero()
        {
            var arg0 = builder.ConstantBV(0, 4);

            var neg = builder.BVNEG(arg0);
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(neg);
            Assert.IsInstanceOf<LiteralExpr>(result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(new BigInteger(0), ( result as LiteralExpr ).asBvConst.Value.ToBigInteger);
            Assert.IsTrue(builder.ConstantBV(0, 4).Equals(result));
        }
    }
}

