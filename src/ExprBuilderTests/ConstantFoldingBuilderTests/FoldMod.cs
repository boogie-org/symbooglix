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
    public class FoldMod : ConstantFoldingExprBuilderTests
    {
        // m div n = q
        // m mod n = r
        // nq + r = m
        // 0 <= r <= ( |n| =-1 )
        [TestCase(1, 1, 0)]
        [TestCase(11, 3, 2)]  // q = 3
        [TestCase(11, -3, 2)] // q = -3
        [TestCase(-11, 3, 1)]  // q = -4
        [TestCase(-11, -3, 1)] // q = 4
        public void ModSimpleConstantsInt(int m, int n, int r)
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Mod(cfb.ConstantInt(m), cfb.ConstantInt(n));
            CheckIsInt(result);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.AreEqual(BigNum.FromInt(r), asLit.asBigNum);
        }

        [Test()]
        public void ModByZero()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Mod(cfb.ConstantInt(8), cfb.ConstantInt(0));
            CheckIsInt(result);
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsMod(result));
            Assert.AreEqual("8 mod 0", result.ToString());
        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var v1 = GetVarAndIdExpr("y", BasicType.Int);
            var foldedResult = cfb.Mod(v0.Item2, v1.Item2);
            var simpleResult = sfb.Mod(v0.Item2, v1.Item2);
            CheckIsInt(foldedResult);
            CheckIsInt(simpleResult);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

