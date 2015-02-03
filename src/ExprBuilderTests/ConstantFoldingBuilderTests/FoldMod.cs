using NUnit.Framework;
using System;
using System.Collections;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldMod : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void ModSimpleConstantsInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Mod(cfb.ConstantInt(10), cfb.ConstantInt(3));
            Assert.IsInstanceOf<LiteralExpr>(result);
            CheckType(result, p => p.IsInt);
            Assert.AreEqual("1", result.ToString());
        }

        [Test()]
        public void ModByZero()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Mod(cfb.ConstantInt(8), cfb.ConstantInt(0));
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsMod(result));
            Assert.AreEqual("8 mod 0", result.ToString());
        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var v1 = GetVarAndIdExpr("y", BasicType.Int);
            var foldedResult = cfb.Mod(v0.Item2, v1.Item2);
            var simpleResult = sfb.Mod(v0.Item2, v1.Item2);
            CheckType(foldedResult, p => p.IsInt);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

