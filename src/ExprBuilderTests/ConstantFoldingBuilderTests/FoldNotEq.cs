using System;
using NUnit.Framework;
using Symbooglix;

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
    }
}

