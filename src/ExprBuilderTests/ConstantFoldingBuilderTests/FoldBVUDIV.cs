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
    public class FoldBVUDIV : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 5, 4, 0)]
        [TestCase(1, 1, 2, 1)]
        [TestCase(10, 7, 4, 1)]
        [TestCase(1, 4, 4, 0)]
        [TestCase(2, 4, 4, 0)]
        [TestCase(3, 4, 4, 0)]
        [TestCase(4, 4, 4, 1)]
        [TestCase(5, 4, 4, 1)]
        [TestCase(6, 4, 4, 1)]
        [TestCase(7, 4, 4, 1)]
        [TestCase(8, 4, 4, 2)]
        [TestCase(9, 4, 4, 2)]
        [TestCase(10, 4, 4, 2)]
        [TestCase(11, 4, 4, 2)]
        [TestCase(12, 4, 4, 3)]
        [TestCase(13, 4, 4, 3)]
        [TestCase(14, 4, 4, 3)]
        [TestCase(15, 4, 4, 3)]
        // Large divisor
        [TestCase(0, 9, 4, 0)]
        [TestCase(1, 9, 4, 0)]
        [TestCase(2, 9, 4, 0)]
        [TestCase(3, 9, 4, 0)]
        [TestCase(4, 9, 4, 0)]
        [TestCase(5, 9, 4, 0)]
        [TestCase(6, 9, 4, 0)]
        [TestCase(7, 9, 4, 0)]
        [TestCase(8, 9, 4, 0)]
        [TestCase(9, 9, 4, 1)]
        [TestCase(10, 9, 4, 1)]
        [TestCase(11, 9, 4, 1)]
        [TestCase(12, 9, 4, 1)]
        [TestCase(13, 9, 4, 1)]
        [TestCase(14, 9, 4, 1)]
        [TestCase(15, 9, 4, 1)]
        public void SimpleConstants(int dividendValue, int divisorValue, int bitWidth, int expectedValue)
        {
            var cfb = GetConstantFoldingBuilder();
            var dividend = cfb.ConstantBV(dividendValue, bitWidth);
            var divisor = cfb.ConstantBV(divisorValue, bitWidth);
            var result = cfb.BVUDIV(dividend, divisor);
            CheckIsBvType(result, bitWidth);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
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

            var noFoldResult = sfb.BVUDIV(dividend, divisor);
            var cfbNoFold = cfb.BVUDIV(dividend, divisor);
            CheckIsBvType(cfbNoFold, 4);
            CheckIsBvType(noFoldResult, 4);
            Assert.IsNull(ExprUtil.AsLiteral(cfbNoFold));
            Assert.IsTrue(ExprUtil.StructurallyEqual(noFoldResult, cfbNoFold));
        }

        [Test()]
        public void DivideByOne()
        {
            var cfb = GetConstantFoldingBuilder();
            var dividend = GetVarAndIdExpr("x", BasicType.GetBvType(4)).Item2;
            var divisor = cfb.ConstantBV(1, 4);
            var result = cfb.BVUDIV(dividend, divisor);
            CheckIsBvType(result, 4);
            Assert.IsTrue(ExprUtil.StructurallyEqual(result, dividend));
        }

        [Test()]
        public void NoFold()
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            SimpleExprBuilder sfb = builders.Item1;
            ConstantFoldingExprBuilder cfb = builders.Item2;
            var arg0 = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var arg1 = GetVarAndIdExpr("y", BasicType.GetBvType(8)).Item2;
            var simpleResult = sfb.BVUDIV(arg0, arg1);
            var result = cfb.BVUDIV(arg0, arg1);
            CheckIsBvType(result, 8);
            CheckIsBvType(simpleResult, 8);

            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsBVUDIV(result));
            Assert.IsTrue(ExprUtil.StructurallyEqual(result, simpleResult));
        }
    }
}

