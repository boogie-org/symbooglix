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
    public class FoldBVSEXT : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 4, 8, 0)]
        [TestCase(1, 4, 8, 1)]
        [TestCase(2, 4, 8, 2)]
        [TestCase(3, 4, 8, 3)]
        [TestCase(4, 4, 8, 4)]
        [TestCase(5, 4, 8, 5)]
        [TestCase(6, 4, 8, 6)]
        [TestCase(7, 4, 8, 7)]
        [TestCase(8, 4, 8, 248)]
        [TestCase(9, 4, 8, 249)]
        [TestCase(10, 4, 8, 250)]
        [TestCase(11, 4, 8, 251)]
        [TestCase(12, 4, 8, 252)]
        [TestCase(13, 4, 8, 253)]
        [TestCase(14, 4, 8, 254)]
        [TestCase(15, 4, 8, 255)]
        public void simpleConstants(int decimalValue, int bitWidth, int newBitWidth, int expectedValueInDecimalRepr)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.BVSEXT(cfb.ConstantBV(decimalValue, bitWidth), newBitWidth);
            CheckIsBvType(result, newBitWidth);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(asLit.isBvConst);
            Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(expectedValueInDecimalRepr), asLit.asBvConst.Value);
        }

        [TestCase(1)]
        [TestCase(2)]
        [TestCase(50)]
        public void nestedBVSEXT(int depth)
        {
            var pair = GetVarAndIdExpr("foo", BasicType.GetBvType(8));
            var variable = pair.Item1;
            var id = pair.Item2;
            var cfb = GetConstantFoldingBuilder();
            Expr result = cfb.BVSEXT(id, 8);
            Assert.IsNotNull(ExprUtil.AsBVSEXT(result));
            Expr root = result;
            for (int i = 0; i < depth; ++i)
            {
                // Sign extending to the same width should be a no-op
                result = cfb.BVSEXT(result, 8);
                CheckIsBvType(result, 8);
            }

            Assert.AreSame(root, result);
        }

        [Test()]
        public void noFold()
        {
            var pair = GetSimpleAndConstantFoldingBuilder();
            var sb = pair.Item1;
            var cfb = pair.Item2;
            var id = GetVarAndIdExpr("foo", BasicType.GetBvType(8)).Item2;
            var foldedResult = cfb.BVSEXT(id, 16);
            var simpleResult = sb.BVSEXT(id, 16);
            CheckIsBvType(simpleResult, 16);
            CheckIsBvType(foldedResult, 16);
            Assert.AreEqual(simpleResult, foldedResult);

            var asBvSExt = ExprUtil.AsBVSEXT(foldedResult);
            Assert.IsNotNull(asBvSExt);
            Assert.AreSame(id, asBvSExt.Args[0]);
        }
    }
}

