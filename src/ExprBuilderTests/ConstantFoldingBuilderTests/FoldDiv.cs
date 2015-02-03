using NUnit.Framework;
using System;
using System.Collections;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldDiv : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void DivideSimpleConstantsInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Div(cfb.ConstantInt(8), cfb.ConstantInt(3));
            Assert.IsInstanceOf<LiteralExpr>(result);
            CheckType(result, p => p.IsInt);
            Assert.AreEqual("2", result.ToString());
        }

        [Test()]
        public void DivideByZero()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Div(cfb.ConstantInt(8), cfb.ConstantInt(0));
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsDiv(result));
            Assert.AreEqual("8 div 0", result.ToString());
        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var v1 = GetVarAndIdExpr("y", BasicType.Int);
            var foldedResult = cfb.Div(v0.Item2, v1.Item2);
            var simpleResult = sfb.Div(v0.Item2, v1.Item2);
            CheckType(foldedResult, p => p.IsInt);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

