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
    public class FoldBVNEG : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 4, 0)]
        [TestCase(1, 4, 15)]
        [TestCase(2, 4, 14)]
        [TestCase(3, 4, 13)]
        [TestCase(4, 4, 12)]
        [TestCase(5, 4, 11)]
        [TestCase(6, 4, 10)]
        [TestCase(7, 4, 9)]
        [TestCase(8, 4, 8)]
        [TestCase(9, 4, 7)]
        [TestCase(10, 4, 6)]
        [TestCase(11, 4, 5)]
        [TestCase(12, 4, 4)]
        [TestCase(13, 4, 3)]
        [TestCase(14, 4, 2)]
        [TestCase(15, 4, 1)]
        public void simpleConstants(int decimalValue, int bitWidth, int expectedValueInDecimalRepr)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.BVNEG(cfb.ConstantBV(decimalValue, bitWidth));
            CheckIsBvType(result, bitWidth);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(asLit.isBvConst);
            Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(expectedValueInDecimalRepr), asLit.asBvConst.Value);
        }

        [TestCase(2)]
        [TestCase(3)]
        [TestCase(50)]
        public void nestedNegs(int depth)
        {
            var pair = GetVarAndIdExpr("foo", BasicType.GetBvType(8));
            var variable = pair.Item1;
            var id = pair.Item2;
            var cfb = GetConstantFoldingBuilder();
            Expr result = id;
            for (int i = 0; i < depth; ++i)
            {
                result = cfb.BVNEG(result);
                CheckIsBvType(result, 8);
            }

            if (depth % 2 == 0)
            {
                Assert.AreSame(id, result);
            }
            else
            {
                var asBvNeg = ExprUtil.AsBVNEG(result);
                Assert.IsNotNull(asBvNeg);
                Assert.AreSame(id, asBvNeg.Args[0]);
            }
        }

        [Test()]
        public void noFold()
        {
            var pair = GetSimpleAndConstantFoldingBuilder();
            var sb = pair.Item1;
            var cfb = pair.Item2;
            var id = GetVarAndIdExpr("foo", BasicType.GetBvType(8)).Item2;
            var foldedResult = cfb.BVNEG(id);
            var simpleResult = sb.BVNEG(id);
            CheckIsBvType(foldedResult, 8);
            CheckIsBvType(simpleResult, 8);
            Assert.AreEqual(simpleResult, foldedResult);

            var asBvNeg = ExprUtil.AsBVNEG(foldedResult);
            Assert.IsNotNull(asBvNeg);
            Assert.AreSame(id, asBvNeg.Args[0]);
        }
    }
}

