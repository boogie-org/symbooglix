using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldAnd : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void TrueAndTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.And(cfb.True, cfb.True);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void TrueAndFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.And(cfb.True, cfb.False);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void FalseAndTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.And(cfb.False, cfb.True);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void FalseAndFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.And(cfb.False, cfb.False);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void FalseAndVar()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.And(cfb.False, variable);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void VarAndFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.And(variable, cfb.False);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void TrueAndVar()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.And(cfb.True, variable);
            Assert.AreSame(variable, result);
        }

        [Test()]
        public void VarAndTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.And(variable, cfb.True);
            Assert.AreSame(variable, result);
        }

        [Test()]
        public void SameExprLhsAndRhs()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable0 = GetVarAndIdExpr("foo", BasicType.Int).Item2;
            var variable1 = GetVarAndIdExpr("foo2", BasicType.Int).Item2;
            var side = cfb.Gt(variable0, variable1);
            var result = cfb.And(side, side);
            Assert.AreSame(side, result);
        }

        [Test()]
        public void NoFold()
        {
            var pair = GetSimpleAndConstantFoldingBuilder();
            var sb = pair.Item1;
            var cfb = pair.Item2;
            var variable0 = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var variable1 = GetVarAndIdExpr("foo2", BasicType.Bool).Item2;
            var foldedResult = cfb.And(variable0, variable1);
            var simpleResult = sb.And(variable0, variable1);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

