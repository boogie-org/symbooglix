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
    public class FoldBVOR : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 0, 4, 0)]
        [TestCase(10, 5, 4, 15)]
        [TestCase(15, 15, 4, 15)]
        [TestCase(15, 6, 4, 15)]
        [TestCase(6, 15, 4, 15)]
        [TestCase(12, 15, 4, 15)]
        [TestCase(15, 12, 4, 15)]
        [TestCase(12, 3, 4, 15)]
        [TestCase(3, 12, 4, 15)]
        [TestCase(1, 2, 4, 3)]
        [TestCase(8, 2, 4, 10)]
        [TestCase(4, 3, 4, 7)]
        public void OrSimpleConstants(int lhsValueDecRepr, int rhsValueDecRepr, int bitWidth, int expectedValueDecRepr)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.BVOR(cfb.ConstantBV(lhsValueDecRepr, bitWidth), cfb.ConstantBV(rhsValueDecRepr, bitWidth));
            CheckIsBvType(result, bitWidth);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(expectedValueDecRepr), asLit.asBvConst.Value);
        }

        [Test()]
        public void OrWithZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVOR(id, cfb.ConstantBV(0, 8));
            CheckIsBvType(result, 8);
            Assert.AreSame(id, result);
        }

        [Test()]
        public void OrWithAllOnes()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var allOnes = cfb.ConstantBV(255, 8);
            var result = cfb.BVOR(id, allOnes);
            CheckIsBvType(result, 8);
            Assert.AreSame(allOnes, result);
        }

        [Test()]
        public void OrWithSameExpr()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVOR(id, id);
            CheckIsBvType(result, 8);
            Assert.AreSame(id, result);
        }


        [Test()]
        public void BVORAssociativityPropagateConstantUp()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            Expr foldedResult = sb.ConstantBV(5, 4);
            Expr unfoldedResult = foldedResult;

            for (int index = 0; index < 3; ++index)
            {
                var x = GetVarAndIdExpr("x" + index.ToString(), BasicType.GetBvType(4)).Item2;
                foldedResult = cfb.BVOR(x, foldedResult);
                unfoldedResult = sb.BVOR(x, unfoldedResult);
                CheckIsBvType(foldedResult, 4);
                CheckIsBvType(unfoldedResult, 4);
            }

            Assert.AreEqual("BVOR4(x2, BVOR4(x1, BVOR4(x0, 5bv4)))", unfoldedResult.ToString());
            Assert.AreEqual("BVOR4(5bv4, BVOR4(x2, BVOR4(x1, x0)))", foldedResult.ToString());
            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            var topAsBVOR = ExprUtil.AsBVOR(foldedResult);
            Assert.IsNotNull(topAsBVOR);
            // Check the constant is the top left argument
            Assert.IsNotNull(ExprUtil.AsLiteral(topAsBVOR.Args[0]));
        }


        [Test()]
        public void BVORAssociativityAddNearbyConstants()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            var x = GetVarAndIdExpr("x", BasicType.GetBvType(4)).Item2;

            Expr foldedResult = x;
            Expr unfoldedResult = foldedResult;

            for (int index = 1; index <= 3; ++index)
            {
                foldedResult = cfb.BVOR(cfb.ConstantBV(5, 4), foldedResult);
                unfoldedResult = sb.BVOR(sb.ConstantBV(5, 4), unfoldedResult);
                CheckIsBvType(foldedResult, 4);
                CheckIsBvType(unfoldedResult, 4);
            }
            Assert.AreEqual("BVOR4(5bv4, BVOR4(5bv4, BVOR4(5bv4, x)))", unfoldedResult.ToString());
            Assert.AreEqual("BVOR4(5bv4, x)", foldedResult.ToString());

            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            var topAsBVOR = ExprUtil.AsBVOR(foldedResult);
            Assert.IsNotNull(topAsBVOR);
            // Check the constant is the top left argument
            Assert.IsNotNull(ExprUtil.AsLiteral(topAsBVOR.Args[0]));;
        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.GetBvType(8));
            var v1 = GetVarAndIdExpr("y", BasicType.GetBvType(8));
            var foldedResult = cfb.BVOR(v0.Item2, v1.Item2);
            var simpleResult = sfb.BVOR(v0.Item2, v1.Item2);
            CheckIsBvType(foldedResult, 8);
            CheckIsBvType(simpleResult, 8);
            Assert.IsNotNull(ExprUtil.AsBVOR(foldedResult));
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

