using NUnit.Framework;
using System;
using System.Numerics;
using Symbooglix;
using Microsoft.Boogie;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBnot : TestBase
    {
        [Test()]
        public void Positive()
        {
            var arg0 = builder.ConstantBV(7, 4);

            var neg = builder.BVNOT(arg0);
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(neg);
            Assert.IsInstanceOf<LiteralExpr>(result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(new BigInteger(8), ( result as LiteralExpr ).asBvConst.Value.ToBigInteger);
            Assert.IsTrue(builder.ConstantBV(8, 4).Equals(result));
        }

        [Test()]
        public void Negative()
        {
            var arg0 = builder.ConstantBV(-5, 4);

            var neg = builder.BVNOT(arg0);
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(neg);
            Assert.IsInstanceOf<LiteralExpr>(result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(new BigInteger(4), ( result as LiteralExpr ).asBvConst.Value.ToBigInteger);
            Assert.IsTrue(builder.ConstantBV(4, 4).Equals(result));
        }

        [Test()]
        public void Zero()
        {
            var arg0 = builder.ConstantBV(0, 4);

            var neg = builder.BVNOT(arg0);
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(neg);
            Assert.IsInstanceOf<LiteralExpr>(result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(new BigInteger(15), ( result as LiteralExpr ).asBvConst.Value.ToBigInteger);
            Assert.IsTrue(builder.ConstantBV(15, 4).Equals(result));
        }
    }
}

