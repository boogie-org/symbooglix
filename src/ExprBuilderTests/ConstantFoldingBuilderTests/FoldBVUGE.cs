//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2017 Daniel Liew
//
// This file is licensed under the MIT license.
// See LICENSE.txt for details.
//------------------------------------------------------------------------------
using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBVUGE : ConstantFoldingExprBuilderTests
    {
        // lhs +ve and rhs +ve
        [TestCase(0, 0, 4, true)]
        [TestCase(1, 1, 4, true)]
        [TestCase(2, 1, 4, true)]
        [TestCase(1, 2, 4, false)]
        [TestCase(0, 8, 4, false)]
        [TestCase(1, 9, 4, false)]
        [TestCase(8, 0, 4, true)]
        [TestCase(9, 1, 4, true)]
        [TestCase(15, 8, 4, true)]
        [TestCase(8, 15, 4, false)]
        public void simpleBVUGE(int lhsValue, int rhsValue, int bitWidth, bool expectedTruth)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.BVUGE(cfb.ConstantBV(lhsValue, bitWidth), cfb.ConstantBV(rhsValue, bitWidth));
            CheckIsBoolType(result);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.AreEqual(expectedTruth, asLit.asBool);
        }

        [Test()]
        public void EqualExpr()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVUGE(id, id);
            CheckIsBoolType(result);
            Assert.IsNotNull(ExprUtil.AsLiteral(result));
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void NoFold()
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            SimpleExprBuilder sfb = builders.Item1;
            ConstantFoldingExprBuilder cfb = builders.Item2;
            var arg0 = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var arg1 = GetVarAndIdExpr("y", BasicType.GetBvType(8)).Item2;
            var simpleResult = sfb.BVUGE(arg0, arg1);
            var result = cfb.BVUGE(arg0, arg1);
            CheckIsBoolType(result);
            CheckIsBoolType(simpleResult);
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsBVUGE(result));
            Assert.IsTrue(ExprUtil.StructurallyEqual(result, simpleResult));
        }

    }
}

