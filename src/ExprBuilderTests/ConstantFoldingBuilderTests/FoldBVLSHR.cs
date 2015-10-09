//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using NUnit.Framework;
using System;
using System.Collections;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBVLSHR : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 0, 4, 0)]
        [TestCase(15, 3, 4, 1)]
        [TestCase(15, 4, 4, 0)] // Overshift
        [TestCase(5, 0, 4, 5)]
        [TestCase(5, 1, 4, 2)]
        [TestCase(12, 0, 4, 12)]
        [TestCase(12, 1, 4, 6)]
        [TestCase(13, 0, 4, 13)]
        [TestCase(13, 1, 4, 6)]
        public void ShiftLeftSimpleConstants(int lhsValueDecRepr, int rhsValueDecRepr, int bitWidth, int expectedValueDecRepr)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.BVLSHR(cfb.ConstantBV(lhsValueDecRepr, bitWidth), cfb.ConstantBV(rhsValueDecRepr, bitWidth));
            CheckIsBvType(result, bitWidth);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(expectedValueDecRepr), asLit.asBvConst.Value);
        }

        [TestCase(4, 4)]
        [TestCase(4, 5)]
        [TestCase(8, 8)]
        [TestCase(8, 16)]
        public void OvershiftExpr(int bitWidth, int shiftWidth)
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(bitWidth)).Item2;
            var result = cfb.BVLSHR(id, cfb.ConstantBV(shiftWidth, bitWidth));
            CheckIsBvType(result, bitWidth);
            Assert.IsTrue(ExprUtil.IsZero(result));
        }

        [Test()]
        public void ShiftByZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVLSHR(id, cfb.ConstantBV(0, 8));
            CheckIsBvType(result, 8);
            Assert.AreSame(id, result);
        }

        [Test()]
        public void ShiftZeroByExpr()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVLSHR(cfb.ConstantBV(0, 8), id);
            CheckIsBvType(result, 8);
            Assert.IsTrue(ExprUtil.IsZero(result));
        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.GetBvType(8));
            var v1 = GetVarAndIdExpr("y", BasicType.GetBvType(8));
            var foldedResult = cfb.BVLSHR(v0.Item2, v1.Item2);
            var simpleResult = sfb.BVLSHR(v0.Item2, v1.Item2);
            CheckIsBvType(foldedResult, 8);
            CheckIsBvType(simpleResult, 8);
            Assert.IsNotNull(ExprUtil.AsBVLSHR(foldedResult));
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

