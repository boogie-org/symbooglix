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
    public class FoldNotEq : ConstantFoldingExprBuilderTests
    {
        [TestCase(true, true, false)]
        [TestCase(true, false, true)]
        [TestCase(false, true, true)]
        [TestCase(false, false, false)]
        public void simpleConstantBool(bool lhs, bool rhs, bool truth)
        {
            var cfb = GetConstantFoldingBuilder();
            var constant0 = cfb.ConstantBool(lhs);
            var constant1 = cfb.ConstantBool(rhs);
            var result = cfb.NotEq(constant0, constant1);
            CheckIsBoolType(result);
            if (truth)
                Assert.IsTrue(ExprUtil.IsTrue(result));
            else
                Assert.IsTrue(ExprUtil.IsFalse(result));
        }


        [TestCase(0, 0, 4, false)]
        [TestCase(0, 1, 4, true)]
        [TestCase(1, 0, 4, true)]
        public void simpleConstantBv(int lhsDecRepr, int rhsDecRepr, int bitWidth, bool truth)
        {
            var cfb = GetConstantFoldingBuilder();
            var constant0 = cfb.ConstantBV(lhsDecRepr, 4);
            var constant1 = cfb.ConstantBV(rhsDecRepr, 4);
            var result = cfb.NotEq(constant0, constant1);
            CheckIsBoolType(result);
            if (truth)
                Assert.IsTrue(ExprUtil.IsTrue(result));
            else
                Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [TestCase(0, 0, false)]
        [TestCase(0, 1, true)]
        [TestCase(1, -1, true)]
        [TestCase(2, -1, true)]
        [TestCase(2, -2, true)]
        [TestCase(1, 1, false)]
        public void simpleConstantInt(int lhs, int rhs, bool truth)
        {
            var cfb = GetConstantFoldingBuilder();
            var constant0 = cfb.ConstantInt(lhs);
            var constant1 = cfb.ConstantInt(rhs);
            var result = cfb.NotEq(constant0, constant1);
            CheckIsBoolType(result);
            if (truth)
                Assert.IsTrue(ExprUtil.IsTrue(result));
            else
                Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [TestCase("0.0", "0.0", false)]
        [TestCase("0.0", "0.1", true)]
        [TestCase("0.1", "0.0", true)]
        [TestCase("-0.0", "0.0", false)]
        [TestCase("15.0", "15.0001", true)]
        public void simpleConstantReal(string lhs, string rhs, bool truth)
        {
            var cfb = GetConstantFoldingBuilder();
            var constant0 = cfb.ConstantReal(lhs);
            var constant1 = cfb.ConstantReal(rhs);
            var result = cfb.NotEq(constant0, constant1);
            CheckIsBoolType(result);
            if (truth)
                Assert.IsTrue(ExprUtil.IsTrue(result));
            else
                Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void foldSameExpr()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var side = cfb.Add(v0.Item2, v0.Item2);
            var foldedResult = cfb.NotEq(side, side);
            CheckIsBoolType(foldedResult);
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
            CheckIsBoolType(foldedResult);
            CheckIsBoolType(simpleResult);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

