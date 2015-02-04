using System;
using NUnit.Framework;
using Microsoft.Boogie;
using System.Collections.Generic;
using Symbooglix;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldExists : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void TrueBody()
        {
            var cfb = GetConstantFoldingBuilder();
            var xPair = GetBoundVarAndIdExpr("x", BasicType.Int);
            var freeVarX = xPair.Item1;
            var x = xPair.Item2;
            var result = cfb.Exists(new List<Variable>() {freeVarX}, cfb.True);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void FalseBody()
        {
            var cfb = GetConstantFoldingBuilder();
            var xPair = GetBoundVarAndIdExpr("x", BasicType.Int);
            var freeVarX = xPair.Item1;
            var x = xPair.Item2;
            var result = cfb.Exists(new List<Variable>() {freeVarX}, cfb.False);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void NoFold()
        {
            var pair = GetSimpleAndConstantFoldingBuilder();
            var sb = pair.Item1;
            var cfb = pair.Item2;
            var xPair = GetBoundVarAndIdExpr("x", BasicType.Int);
            var freeVarX = xPair.Item1;
            var x = xPair.Item2;

            var yPair = GetBoundVarAndIdExpr("y", BasicType.Int);
            var freeVarY = yPair.Item1;
            var y = yPair.Item2;

            var foldedResult = cfb.Exists(new List<Variable>() { freeVarX, freeVarY}, cfb.Lt(x,y));
            var simpleResult = sb.Exists(new List<Variable>() {freeVarX, freeVarY}, sb.Lt(x,y));
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

