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
    public class FoldBVZEXT : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 4, 8, 0)]
        [TestCase(1, 4, 8, 1)]
        [TestCase(2, 4, 8, 2)]
        [TestCase(3, 4, 8, 3)]
        [TestCase(4, 4, 8, 4)]
        [TestCase(5, 4, 8, 5)]
        [TestCase(6, 4, 8, 6)]
        [TestCase(7, 4, 8, 7)]
        [TestCase(8, 4, 8, 8)]
        [TestCase(9, 4, 8, 9)]
        [TestCase(10, 4, 8, 10)]
        [TestCase(11, 4, 8, 11)]
        [TestCase(12, 4, 8, 12)]
        [TestCase(13, 4, 8, 13)]
        [TestCase(14, 4, 8, 14)]
        [TestCase(15, 4, 8, 15)]
        public void simpleConstants(int decimalValue, int bitWidth, int newBitWidth, int expectedValueInDecimalRepr)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.BVZEXT(cfb.ConstantBV(decimalValue, bitWidth), newBitWidth);
            CheckIsBvType(result, newBitWidth);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(asLit.isBvConst);
            Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(expectedValueInDecimalRepr), asLit.asBvConst.Value);
        }

        [TestCase(1)]
        [TestCase(2)]
        [TestCase(50)]
        public void nestedBVZEXT(int depth)
        {
            var pair = GetVarAndIdExpr("foo", BasicType.GetBvType(4));
            var variable = pair.Item1;
            var id = pair.Item2;
            var cfb = GetConstantFoldingBuilder();
            Expr result = cfb.BVZEXT(id, 8);
            Assert.IsNotNull(ExprUtil.AsBVZEXT(result));
            for (int i = 0; i < depth; ++i)
            {
                // The newest (closest to the root) zero_extend superseeds any below
                result = cfb.BVZEXT(result, 8 + i);
                CheckIsBvType(result, 8 + i);
            }

            CheckIsBvType(result, depth + 8 -1);
            var asBvZext = ExprUtil.AsBVZEXT(result);
            Assert.IsNotNull(asBvZext);
            Assert.AreSame(id, asBvZext.Args[0]);
        }

        [Test()]
        public void noFold()
        {
            var pair = GetSimpleAndConstantFoldingBuilder();
            var sb = pair.Item1;
            var cfb = pair.Item2;
            var id = GetVarAndIdExpr("foo", BasicType.GetBvType(8)).Item2;
            var foldedResult = cfb.BVZEXT(id, 16);
            var simpleResult = sb.BVZEXT(id, 16);
            CheckIsBvType(foldedResult, 16);
            CheckIsBvType(simpleResult, 16);
            Assert.AreEqual(simpleResult, foldedResult);

            var asBvZExt = ExprUtil.AsBVZEXT(foldedResult);
            Assert.IsNotNull(asBvZExt);
            Assert.AreSame(id, asBvZExt.Args[0]);
        }
    }
}

