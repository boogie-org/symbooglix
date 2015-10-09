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
    public class FoldBVEXTRACT : ConstantFoldingExprBuilderTests
    {
        // Extract single bit
        [TestCase(15, 4, 4, 3, 1)]
        [TestCase(15, 4, 1, 0, 1)]
        [TestCase(0, 4, 4, 3, 0)]
        [TestCase(10, 4, 4, 3, 1)]
        [TestCase(10, 4, 3, 2, 0)]
        [TestCase(10, 4, 2, 1, 1)]
        [TestCase(10, 4, 1, 0, 0)]
        [TestCase(-1, 32, 32, 31, 1)]
        // Extract half
        [TestCase(15, 4, 4, 2, 3)]
        [TestCase(10, 4, 4, 2, 2)]
        [TestCase(10, 4, 2, 0, 2)]
        [TestCase(12, 4, 2, 0, 0)]
        public void simpleConstants(int decimalValue, int bitWidth, int end, int start, int expectedValueInDecimalRepr)
        {
            Assert.IsTrue(end > start);
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.BVEXTRACT(cfb.ConstantBV(decimalValue, bitWidth), end, start);
            CheckIsBvType(result, end - start);
            var asLit = ExprUtil.AsLiteral(result);
            CheckIsBvType(result, end - start);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(asLit.isBvConst);
            Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(expectedValueInDecimalRepr), asLit.asBvConst.Value);
        }

        [TestCase(15, 4, true)]
        [TestCase(7, 4, false)]
        [TestCase(-1, 256, true)]
        [TestCase(0, 256, false)]
        public void nestedBVEXTRACTConstant(int initialValue, int bitWidth, bool bitIsTrue)
        {
            var cfb = GetConstantFoldingBuilder();
            var constant = cfb.ConstantBV(initialValue, bitWidth);
            Expr result = constant;

            // Keep peeling off the least significant bit until we're only left
            // with the most significant bit
            for (int count = 0; count < bitWidth - 1; ++count)
            {
                int topBitPlusOne = bitWidth - count;
                result = cfb.BVEXTRACT(result, topBitPlusOne, 1);
            }

            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            CheckIsBvType(asLit, 1);
            if (bitIsTrue)
                Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(1), asLit.asBvConst.Value);
            else
                Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(0), asLit.asBvConst.Value);
        }

        [TestCase(5)]
        [TestCase(256)]
        [TestCase(512)]
        public void SelectWholeBitVector(int bitWidth)
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("foo", BasicType.GetBvType(bitWidth)).Item2;
            var result = cfb.BVEXTRACT(id, bitWidth, 0);
            CheckIsBvType(result, bitWidth);
            Assert.AreSame(id, result);
        }

        [TestCase(4)]
        [TestCase(8)]
        [TestCase(32)]
        [TestCase(64)]
        [TestCase(128)]
        [TestCase(256)]
        [TestCase(512)]
        public void nestedBVEXTRACTVariableStart(int bitWidth)
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(bitWidth)).Item2;
            Expr result = id;

            // Keep peeling off the most significant bit until we're only left
            // with the least significant bit
            for (int count = 0; count < bitWidth - 1; ++count)
            {
                int topBitMinusOne = result.Type.BvBits - 1;
                result = cfb.BVEXTRACT(result, topBitMinusOne, 0);
                CheckIsBvType(result, bitWidth - count - 1);
            }

            var asBvExtract = ExprUtil.AsBVEXTRACT(result);
            Assert.IsNotNull(asBvExtract);
            CheckIsBvType(asBvExtract, 1);

            // Check there is only a single BvExtractExpr
            Assert.AreSame(id, asBvExtract.Bitvector);
            Assert.AreEqual(1, asBvExtract.End);
            Assert.AreEqual(0, asBvExtract.Start);
        }

        [TestCase(4)]
        [TestCase(8)]
        [TestCase(32)]
        [TestCase(64)]
        [TestCase(128)]
        [TestCase(256)]
        [TestCase(512)]
        public void nestedBVEXTRACTVariableEnd(int bitWidth)
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(bitWidth)).Item2;
            Expr result = id;

            // Keep peeling off the least significant bit until we're only left
            // with the most significant bit
            for (int count = 0; count < bitWidth - 1; ++count)
            {
                int topBitPlusOne = bitWidth - count;
                result = cfb.BVEXTRACT(result, topBitPlusOne, 1);
                CheckIsBvType(result, bitWidth - count - 1);
            }

            var asBvExtract = ExprUtil.AsBVEXTRACT(result);
            Assert.IsNotNull(asBvExtract);
            CheckIsBvType(asBvExtract, 1);

            // Check there is only a single BvExtractExpr
            Assert.AreSame(id, asBvExtract.Bitvector);
            Assert.AreEqual(bitWidth, asBvExtract.End);
            Assert.AreEqual(bitWidth - 1, asBvExtract.Start);
        }

        [TestCase(3)]
        [TestCase(5)]
        [TestCase(7)]
        [TestCase(9)]
        [TestCase(11)]
        [TestCase(13)]
        [TestCase(25)]
        [TestCase(31)]
        [TestCase(127)]
        [TestCase(129)]
        public void nestedBVEXTRACTVariableMiddle(int bitWidth)
        {
            Assert.IsTrue(bitWidth >= 3 && (bitWidth % 2 == 1));
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(bitWidth)).Item2;
            Expr result = id;

            // Keep peeling off the least significant bit and the most significant bit
            // until we're only left the middle bit in the original "id"
            for (int count = 0; count < bitWidth/2 ; ++count)
            {
                int topBit = result.Type.BvBits - 1;
                result = cfb.BVEXTRACT(result, topBit, 1);
                CheckIsBvType(result, bitWidth - (2*(count +1)));
            }

            var asBvExtract = ExprUtil.AsBVEXTRACT(result);
            Assert.IsNotNull(asBvExtract);
            CheckIsBvType(asBvExtract, 1);

            // Check there is only a single BvExtractExpr
            Assert.AreSame(id, asBvExtract.Bitvector);
            var middleBitIndex = bitWidth / 2;

            Assert.AreEqual(middleBitIndex + 1, asBvExtract.End);
            Assert.AreEqual(middleBitIndex, asBvExtract.Start);
        }

        [Test()]
        public void noFold()
        {
            var pair = GetSimpleAndConstantFoldingBuilder();
            var sb = pair.Item1;
            var cfb = pair.Item2;
            var id = GetVarAndIdExpr("foo", BasicType.GetBvType(8)).Item2;
            var foldedResult = cfb.BVEXTRACT(id, 7, 0);
            var simpleResult = sb.BVEXTRACT(id, 7, 0);
            CheckIsBvType(foldedResult, 7);
            CheckIsBvType(simpleResult, 7);
            Assert.AreEqual(simpleResult, foldedResult);

            var asBvExtract = ExprUtil.AsBVEXTRACT(foldedResult);
            Assert.IsNotNull(asBvExtract);
            Assert.AreSame(id, asBvExtract.Bitvector);
            Assert.AreEqual(0, asBvExtract.Start);
            Assert.AreEqual(7, asBvExtract.End);
        }
    }
}

