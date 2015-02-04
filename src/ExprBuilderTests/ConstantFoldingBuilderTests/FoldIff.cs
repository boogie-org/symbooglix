using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldIff : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void TrueAndTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Iff(cfb.True, cfb.True);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void TrueAndFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Iff(cfb.True, cfb.False);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void FalseAndTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Iff(cfb.False, cfb.True);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void FalseAndFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Iff(cfb.False, cfb.False);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void FalseAndVar()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Iff(cfb.False, variable);
            Assert.AreEqual(cfb.Not(variable), result);
        }

        [Test()]
        public void VarAndFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Iff(variable, cfb.False);
            Assert.AreEqual(cfb.Not(variable), result);
        }

        [Test()]
        public void TrueAndVar()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Iff(cfb.True, variable);
            Assert.AreSame(variable, result);
        }

        [Test()]
        public void VarAndTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Iff(variable, cfb.True);
            Assert.AreSame(variable, result);
        }

        [Test()]
        public void SameExprLhsAndRhs()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable0 = GetVarAndIdExpr("foo", BasicType.Int).Item2;
            var variable1 = GetVarAndIdExpr("foo2", BasicType.Int).Item2;
            var side = cfb.Gt(variable0, variable1);
            var result = cfb.Iff(side, side);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void NoFold()
        {
            var pair = GetSimpleAndConstantFoldingBuilder();
            var sb = pair.Item1;
            var cfb = pair.Item2;
            var variable0 = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var variable1 = GetVarAndIdExpr("foo2", BasicType.Bool).Item2;
            var foldedResult = cfb.Iff(variable0, variable1);
            var simpleResult = sb.Iff(variable0, variable1);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

