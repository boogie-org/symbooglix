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
    public class FoldBVSDIV : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 5, 4, 0)]
        [TestCase(1, 1, 2, 1)]
        [TestCase(10, 7, 4, 0)]
        [TestCase(1, 4, 4, 0)]
        [TestCase(2, 4, 4, 0)]
        [TestCase(3, 4, 4, 0)]
        [TestCase(4, 4, 4, 1)]
        [TestCase(5, 4, 4, 1)]
        [TestCase(6, 4, 4, 1)]
        [TestCase(7, 4, 4, 1)]
        [TestCase(8, 4, 4, 14)]
        [TestCase(9, 4, 4, 15)]
        [TestCase(10, 4, 4, 15)]
        [TestCase(11, 4, 4, 15)]
        [TestCase(12, 4, 4, 15)]
        [TestCase(13, 4, 4, 0)]
        [TestCase(14, 4, 4, 0)]
        [TestCase(15, 4, 4, 0)]
        // Divide by negative
        [TestCase(0, 9, 4, 0)]
        [TestCase(1, 9, 4, 0)]
        [TestCase(2, 9, 4, 0)]
        [TestCase(3, 9, 4, 0)]
        [TestCase(4, 9, 4, 0)]
        [TestCase(5, 9, 4, 0)]
        [TestCase(6, 9, 4, 0)]
        [TestCase(7, 9, 4, 15)]
        [TestCase(8, 9, 4, 1)]
        [TestCase(9, 9, 4, 1)]
        [TestCase(10, 9, 4, 0)]
        [TestCase(11, 9, 4, 0)]
        [TestCase(12, 9, 4, 0)]
        [TestCase(13, 9, 4, 0)]
        [TestCase(14, 9, 4, 0)]
        [TestCase(15, 9, 4, 0)]
        public void SimpleConstants(int dividendValue, int divisorValue, int bitWidth, int expectedValue)
        {
            var cfb = GetConstantFoldingBuilder();
            var dividend = cfb.ConstantBV(dividendValue, bitWidth);
            var divisor = cfb.ConstantBV(divisorValue, bitWidth);
            var result = cfb.BVSDIV(dividend, divisor);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            CheckIsBvType(result, bitWidth);
            Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(expectedValue), asLit.asBvConst.Value);
        }

        [Test()]
        public void DivideByZero()
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            var sfb = builders.Item1;
            var cfb = builders.Item2;
            var dividend = cfb.ConstantBV(5, 4);
            var divisor = cfb.ConstantBV(0, 4);

            var noFoldResult = sfb.BVSDIV(dividend, divisor);
            var cfbNoFold = cfb.BVSDIV(dividend, divisor);
            Assert.IsNull(ExprUtil.AsLiteral(cfbNoFold));
            Assert.IsTrue(ExprUtil.StructurallyEqual(noFoldResult, cfbNoFold));
            CheckIsBvType(cfbNoFold, 4);
        }

        [Test()]
        public void DivideByOne()
        {
            var cfb = GetConstantFoldingBuilder();
            var dividend = GetVarAndIdExpr("x", BasicType.GetBvType(4)).Item2;
            var divisor = cfb.ConstantBV(1, 4);
            var result = cfb.BVSDIV(dividend, divisor);
            Assert.IsTrue(ExprUtil.StructurallyEqual(result, dividend));
            CheckIsBvType(result, 4);
        }

        [Test()]
        public void NoFold()
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            SimpleExprBuilder sfb = builders.Item1;
            ConstantFoldingExprBuilder cfb = builders.Item2;
            var arg0 = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var arg1 = GetVarAndIdExpr("y", BasicType.GetBvType(8)).Item2;
            var simpleResult = sfb.BVSDIV(arg0, arg1);
            var result = cfb.BVSDIV(arg0, arg1);
            CheckIsBvType(result, 8);
            CheckIsBvType(simpleResult, 8);
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsBVSDIV(result));
            Assert.IsTrue(ExprUtil.StructurallyEqual(result, simpleResult));
        }
    }
}

