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
    public class FoldBVULE : ConstantFoldingExprBuilderTests
    {
        // lhs +ve and rhs +ve
        [TestCase(0, 0, 4, true)]
        [TestCase(1, 1, 4, true)]
        [TestCase(2, 1, 4, false)]
        [TestCase(1, 2, 4, true)]
        [TestCase(0, 8, 4, true)]
        [TestCase(1, 9, 4, true)]
        [TestCase(8, 0, 4, false)]
        [TestCase(9, 1, 4, false)]
        [TestCase(15, 8, 4, false)]
        [TestCase(8, 15, 4, true)]
        public void simpleBVULE(int lhsValue, int rhsValue, int bitWidth, bool expectedTruth)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.BVULE(cfb.ConstantBV(lhsValue, bitWidth), cfb.ConstantBV(rhsValue, bitWidth));
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
            var result = cfb.BVULE(id, id);
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
            var simpleResult = sfb.BVULE(arg0, arg1);
            var result = cfb.BVULE(arg0, arg1);
            CheckIsBoolType(result);
            CheckIsBoolType(simpleResult);
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsBVULE(result));
            Assert.IsTrue(ExprUtil.StructurallyEqual(result, simpleResult));
        }

    }
}

