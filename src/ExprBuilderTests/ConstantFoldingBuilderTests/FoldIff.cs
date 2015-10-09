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
    public class FoldIff : ConstantFoldingExprBuilderTests
    {
        [TestCase(true, true, true)]
        [TestCase(true, false, false)]
        [TestCase(false, true, false)]
        [TestCase(false, false, true)]
        public void Constants(bool lhs, bool rhs, bool expectedTrue)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Iff(cfb.ConstantBool(lhs), cfb.ConstantBool(rhs));
            CheckIsBoolType(result);
            if (expectedTrue)
                Assert.IsTrue(ExprUtil.IsTrue(result));
            else
                Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void FalseAndVar()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Iff(cfb.False, variable);
            CheckIsBoolType(result);
            Assert.AreEqual(cfb.Not(variable), result);
        }

        [Test()]
        public void VarAndFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Iff(variable, cfb.False);
            CheckIsBoolType(result);
            Assert.AreEqual(cfb.Not(variable), result);
        }

        [Test()]
        public void TrueAndVar()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Iff(cfb.True, variable);
            CheckIsBoolType(result);
            Assert.AreSame(variable, result);
        }

        [Test()]
        public void VarAndTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Iff(variable, cfb.True);
            CheckIsBoolType(result);
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
            CheckIsBoolType(result);
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
            CheckIsBoolType(foldedResult);
            CheckIsBoolType(simpleResult);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

