using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldOr : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void TrueOrTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Or(cfb.True, cfb.True);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void TrueOrFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Or(cfb.True, cfb.False);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void FalseOrTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Or(cfb.False, cfb.True);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void FalseOrFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Or(cfb.False, cfb.False);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void FalseOrVar()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Or(cfb.False, variable);
            Assert.AreSame(variable, result);
        }

        [Test()]
        public void VarOrFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Or(variable, cfb.False);
            Assert.AreSame(variable, result);
        }

        [Test()]
        public void TrueOrVar()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Or(cfb.True, variable);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void VarOrTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Or(variable, cfb.True);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void SameExprLhsAndRhs()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable0 = GetVarAndIdExpr("foo", BasicType.Int).Item2;
            var variable1 = GetVarAndIdExpr("foo2", BasicType.Int).Item2;
            var side = cfb.Gt(variable0, variable1);
            var result = cfb.Or(side, side);
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
            var foldedResult = cfb.Or(variable0, variable1);
            var simpleResult = sb.Or(variable0, variable1);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

