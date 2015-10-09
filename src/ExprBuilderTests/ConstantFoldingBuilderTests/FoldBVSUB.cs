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
    public class FoldBVSUB : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 0, 2, 0)]
        [TestCase(1, 1, 2, 0)]
        [TestCase(1, 2, 2, 3)]
        [TestCase(2, 2, 2, 0)]
        [TestCase(4, 6, 4, 14)]
        [TestCase(15, 0, 4, 15)]
        [TestCase(15, 1, 4, 14)] // Overflow
        [TestCase(1, 5, 4, 12)]
        public void simpleSub(int lhsValue, int rhsValue, int bitWidth, int expectedValue)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.BVSUB(cfb.ConstantBV(lhsValue, bitWidth), cfb.ConstantBV(rhsValue, bitWidth));
            var asLit = ExprUtil.AsLiteral(result);
            CheckIsBvType(result, bitWidth);
            Assert.IsNotNull(asLit);
            Assert.AreEqual(expectedValue, asLit.asBvConst.Value.ToInt);
        }

        [Test()]
        public void NoFold()
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            SimpleExprBuilder sfb = builders.Item1;
            ConstantFoldingExprBuilder cfb = builders.Item2;
            var arg0 = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var arg1 = GetVarAndIdExpr("y", BasicType.GetBvType(8)).Item2;
            var simpleResult = sfb.BVSUB(arg0, arg1);
            var result = cfb.BVSUB(arg0, arg1);
            CheckIsBvType(result, 8);
            CheckIsBvType(simpleResult, 8);
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsBVSUB(result));
            Assert.IsTrue(ExprUtil.StructurallyEqual(result, simpleResult));
        }

        // 0 - x ==> (bvneg x)
        [Test()]
        public void lhsIsZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVSUB(cfb.ConstantBV(0, 8), x);
            CheckIsBvType(result, 8);
            var asBvNeg = ExprUtil.AsBVNEG(result);
            Assert.IsNotNull(asBvNeg);
            Assert.AreSame(x, asBvNeg.Args[0]);
        }

        // x - 0 ==> x
        [Test()]
        public void rhsIsZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVSUB(x, cfb.ConstantBV(0, 8));
            CheckIsBvType(result, 8);
            Assert.AreSame(x, result);
        }

        // <expr> - <expr> ==> 0
        [Test()]
        public void SameExprAdded()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var y = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVSUB(x, x);
            Assert.IsNotNull(ExprUtil.AsLiteral(result));
            CheckIsBvType(result, 8);
            Assert.IsTrue(ExprUtil.IsZero(result));
        }
    }
}

