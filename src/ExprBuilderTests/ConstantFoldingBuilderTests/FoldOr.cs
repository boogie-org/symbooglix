//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldOr : ConstantFoldingExprBuilderTests
    {
        [TestCase(true, true, true)]
        [TestCase(true, false, true)]
        [TestCase(false, true, true)]
        [TestCase(false, false, false)]
        public void SimpleConstants(bool lhs, bool rhs, bool truth)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Or(cfb.ConstantBool(lhs), cfb.ConstantBool(rhs));
            CheckIsBoolType(result);
            if (truth)
                Assert.IsTrue(ExprUtil.IsTrue(result));
            else
                Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void FalseOrVar()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Or(cfb.False, variable);
            CheckIsBoolType(result);
            Assert.AreSame(variable, result);
        }

        [Test()]
        public void VarOrFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Or(variable, cfb.False);
            CheckIsBoolType(result);
            Assert.AreSame(variable, result);
        }

        [Test()]
        public void TrueOrVar()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Or(cfb.True, variable);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void VarOrTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Or(variable, cfb.True);
            CheckIsBoolType(result);
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
            CheckIsBoolType(result);
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
            CheckIsBoolType(foldedResult);
            CheckIsBoolType(simpleResult);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

