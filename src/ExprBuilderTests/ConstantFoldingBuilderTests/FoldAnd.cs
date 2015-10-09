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
    public class FoldAnd : ConstantFoldingExprBuilderTests
    {
        [TestCase(true, true, true)]
        [TestCase(true, false, false)]
        [TestCase(false, true, false)]
        [TestCase(false, false, false)]
        public void simpleConstants(bool lhs, bool rhs, bool expected)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.And(cfb.ConstantBool(lhs), cfb.ConstantBool(rhs));
            CheckIsBoolType(result);
            Assert.IsNotNull(ExprUtil.AsLiteral(result));
            if (expected)
                Assert.IsTrue(ExprUtil.IsTrue(result));
            else
                Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void FalseAndVar()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.And(cfb.False, variable);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void VarAndFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.And(variable, cfb.False);
            CheckIsBoolType(result);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void TrueAndVar()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.And(cfb.True, variable);
            CheckIsBoolType(result);
            Assert.AreSame(variable, result);
        }

        [Test()]
        public void VarAndTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.And(variable, cfb.True);
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
            var result = cfb.And(side, side);
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
            var foldedResult = cfb.And(variable0, variable1);
            var simpleResult = sb.And(variable0, variable1);
            CheckIsBoolType(simpleResult);
            CheckIsBoolType(foldedResult);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

