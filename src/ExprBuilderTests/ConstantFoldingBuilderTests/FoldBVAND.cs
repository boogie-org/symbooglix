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
    public class FoldBVAND : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 0, 4, 0)]
        [TestCase(10, 5, 4, 0)]
        [TestCase(15, 15, 4, 15)]
        [TestCase(15, 6, 4, 6)]
        [TestCase(6, 15, 4, 6)]
        [TestCase(12, 15, 4, 12)]
        [TestCase(15, 12, 4, 12)]
        [TestCase(12, 3, 4, 0)]
        [TestCase(3, 12, 4, 0)]
        public void AndSimpleConstants(int lhsValueDecRepr, int rhsValueDecRepr, int bitWidth, int expectedValueDecRepr)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.BVAND(cfb.ConstantBV(lhsValueDecRepr, bitWidth), cfb.ConstantBV(rhsValueDecRepr, bitWidth));
            CheckIsBvType(result, bitWidth);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(expectedValueDecRepr), asLit.asBvConst.Value);
        }

        [Test()]
        public void AndWithZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVAND(id, cfb.ConstantBV(0, 8));
            CheckIsBvType(result, 8);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(asLit.isBvConst);
            Assert.IsTrue(ExprUtil.IsZero(asLit));
        }

        [Test()]
        public void AndWithAllOnes()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVAND(id, cfb.ConstantBV(255, 8));
            CheckIsBvType(result, 8);
            Assert.AreSame(id, result);
        }

        [Test()]
        public void AndWithSameExpr()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVAND(id, id);
            CheckIsBvType(result, 8);
            Assert.AreSame(id, result);
        }

        [Test()]
        public void BVANDAssociativityPropagateConstantUp()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            Expr foldedResult = sb.ConstantBV(5, 4);
            Expr unfoldedResult = foldedResult;

            for (int index = 0; index < 3; ++index)
            {
                var x = GetVarAndIdExpr("x" + index.ToString(), BasicType.GetBvType(4)).Item2;
                foldedResult = cfb.BVAND(x, foldedResult);
                unfoldedResult = sb.BVAND(x, unfoldedResult);
                CheckIsBvType(foldedResult, 4);
                CheckIsBvType(unfoldedResult, 4);
            }

            Assert.AreEqual("BVAND4(x2, BVAND4(x1, BVAND4(x0, 5bv4)))", unfoldedResult.ToString());
            Assert.AreEqual("BVAND4(5bv4, BVAND4(x2, BVAND4(x1, x0)))", foldedResult.ToString());
            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            var topAsBVAND = ExprUtil.AsBVAND(foldedResult);
            Assert.IsNotNull(topAsBVAND);
            // Check the constant is the top left argument
            Assert.IsNotNull(ExprUtil.AsLiteral(topAsBVAND.Args[0]));
        }


        [Test()]
        public void BVANDAssociativityAddNearbyConstants()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            var x = GetVarAndIdExpr("x", BasicType.GetBvType(4)).Item2;

            Expr foldedResult = x;
            Expr unfoldedResult = foldedResult;

            for (int index = 1; index <= 3; ++index)
            {
                foldedResult = cfb.BVAND(cfb.ConstantBV(5, 4), foldedResult);
                unfoldedResult = sb.BVAND(sb.ConstantBV(5, 4), unfoldedResult);
                CheckIsBvType(foldedResult, 4);
                CheckIsBvType(unfoldedResult, 4);
            }
            Assert.AreEqual("BVAND4(5bv4, BVAND4(5bv4, BVAND4(5bv4, x)))", unfoldedResult.ToString());
            Assert.AreEqual("BVAND4(5bv4, x)", foldedResult.ToString());

            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            var topAsBVAND = ExprUtil.AsBVAND(foldedResult);
            Assert.IsNotNull(topAsBVAND);
            // Check the constant is the top left argument
            Assert.IsNotNull(ExprUtil.AsLiteral(topAsBVAND.Args[0]));;
        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.GetBvType(8));
            var v1 = GetVarAndIdExpr("y", BasicType.GetBvType(8));
            var foldedResult = cfb.BVAND(v0.Item2, v1.Item2);
            var simpleResult = sfb.BVAND(v0.Item2, v1.Item2);
            CheckIsBvType(foldedResult, 8);
            CheckIsBvType(simpleResult, 8);
            Assert.IsNotNull(ExprUtil.AsBVAND(foldedResult));
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

