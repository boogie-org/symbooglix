using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldNotEq : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void simpleConstantBoolEqual()
        {
            var cfb = GetConstantFoldingBuilder();
            var constant0 = cfb.True;
            var constant1 = cfb.True;
            var result = cfb.NotEq(constant0, constant1);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void simpleConstantBoolNotEqual()
        {
            var cfb = GetConstantFoldingBuilder();
            var constant0 = cfb.False;
            var constant1 = cfb.True;
            var result = cfb.NotEq(constant0, constant1);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void simpleConstantBvEqual()
        {
            var cfb = GetConstantFoldingBuilder();
            var constant0 = cfb.ConstantBV(0, 4);
            var constant1 = cfb.ConstantBV(0, 4);
            var result = cfb.NotEq(constant0, constant1);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void simpleConstantBvNotEqual()
        {
            var cfb = GetConstantFoldingBuilder();
            var constant0 = cfb.ConstantBV(0, 4);
            var constant1 = cfb.ConstantBV(2, 4);
            var result = cfb.NotEq(constant0, constant1);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void simpleConstantIntEqual()
        {
            var cfb = GetConstantFoldingBuilder();
            var constant0 = cfb.ConstantInt(0);
            var constant1 = cfb.ConstantInt(0);
            var result = cfb.NotEq(constant0, constant1);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void simpleConstantIntNotEqual()
        {
            var cfb = GetConstantFoldingBuilder();
            var constant0 = cfb.ConstantInt(0);
            var constant1 = cfb.ConstantInt(1);
            var result = cfb.NotEq(constant0, constant1);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void simpleConstantRealEqual()
        {
            var cfb = GetConstantFoldingBuilder();
            var constant0 = cfb.ConstantReal("0.0");
            var constant1 = cfb.ConstantReal("0.0");
            var result = cfb.NotEq(constant0, constant1);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void simpleConstantRealNotEqual()
        {
            var cfb = GetConstantFoldingBuilder();
            var constant0 = cfb.ConstantReal("0.0");
            var constant1 = cfb.ConstantReal("0.1");
            var result = cfb.NotEq(constant0, constant1);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void foldSameExpr()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var side = cfb.Add(v0.Item2, v0.Item2);
            var foldedResult = cfb.NotEq(side, side);
            CheckType(foldedResult, p => p.IsBool);
            Assert.IsTrue(ExprUtil.IsFalse(foldedResult));
        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var v1 = GetVarAndIdExpr("y", BasicType.Int);
            var foldedResult = cfb.NotEq(v0.Item2, v1.Item2);
            var simpleResult = sfb.NotEq(v0.Item2, v1.Item2);
            CheckType(foldedResult, p => p.IsBool);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

