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
    public class FoldImp : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void TrueAntecedent()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Imp(cfb.True, variable);
            CheckIsBoolType(result);
            Assert.AreSame(variable, result);
        }

        [Test()]
        public void FalseAntecedent()
        {
            var cfb = GetConstantFoldingBuilder();
            var variable = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Imp(cfb.False, variable);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void ExprImpliesExpr()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Bool).Item2;
            var y = GetVarAndIdExpr("y", BasicType.Bool).Item2;
            var side = cfb.And(x, y);
            var result = cfb.Imp(side, side);
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
            var foldedResult = cfb.Imp(variable0, variable1);
            var simpleResult = sb.Imp(variable0, variable1);
            CheckIsBoolType(foldedResult);
            CheckIsBoolType(simpleResult);
            Assert.AreEqual(simpleResult, foldedResult);
            Assert.IsNotNull(ExprUtil.AsImp(foldedResult));
        }
    }
}

