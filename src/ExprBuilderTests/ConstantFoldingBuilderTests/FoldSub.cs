using NUnit.Framework;
using System;
using System.Collections;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldSub : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void SubSimpleConstantsInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Sub(cfb.ConstantInt(5), cfb.ConstantInt(3));
            Assert.IsInstanceOf<LiteralExpr>(result);
            CheckType(result, p => p.IsInt);
            Assert.AreEqual("2", result.ToString());
        }

        [Test()]
        public void SubSimpleConstantsReal()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Sub(cfb.ConstantReal("5.0"), cfb.ConstantReal("3.0"));
            Assert.IsInstanceOf<LiteralExpr>(result);
            CheckType(result, p => p.IsReal);
            Assert.AreEqual("2e0", result.ToString());
        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var v1 = GetVarAndIdExpr("y", BasicType.Int);
            var foldedResult = cfb.Sub(v0.Item2, v1.Item2);
            var simpleResult = sfb.Sub(v0.Item2, v1.Item2);
            CheckType(foldedResult, p => p.IsInt);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

