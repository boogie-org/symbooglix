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
    public class FoldArithmeticCoercion : ConstantFoldingExprBuilderTests
    {
        [TestCase("5.0", 5)]
        [TestCase("5.5", 5)]
        [TestCase("5.9", 5)]
        [TestCase("-5.1", -6)] // FIXME: This is broken in Boogie
        [TestCase("-5.5", -6)] // FIXME: This is broken in Boogie
        [TestCase("-5.8", -6)] // FIXME: This is broken in Boogie
        [TestCase("-5.0", -5)]
        [TestCase("0.0", 0)]
        public void RealToIntSimpleConstantsInt(string operand, int expectedValue)
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToInt, cfb.ConstantReal(operand));
            CheckIsInt(result);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(asLit.isBigNum);
            Assert.AreEqual(BigNum.FromInt(expectedValue), asLit.asBigNum);
        }

        [TestCase(5, "5e0")]
        [TestCase(-5, "-5e0")]
        [TestCase(0, "0e0")]
        public void IntToRealSimpleConstantsInt(int operand, string expectedValue)
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToReal, cfb.ConstantInt(operand));
            CheckIsReal(result);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(asLit.isBigDec);
            Assert.AreEqual(expectedValue, asLit.asBigDec.ToString());
        }

        [Test()]
        public void NoFoldToInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var foldedResult = cfb.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToInt, v0);
            var simpleResult = sfb.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToInt, v0);
            CheckIsInt(foldedResult);
            CheckIsInt(simpleResult);
            Assert.AreEqual(simpleResult, foldedResult);
            Assert.IsNotNull(ExprUtil.AsArithmeticCoercion(foldedResult));
        }

        [Test()]
        public void NoFoldToReal()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var foldedResult = cfb.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToReal, v0);
            var simpleResult = sfb.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToReal, v0);
            CheckIsReal(foldedResult);
            CheckIsReal(simpleResult);
            Assert.AreEqual(simpleResult, foldedResult);
            Assert.IsNotNull(ExprUtil.AsArithmeticCoercion(foldedResult));
        }

    }
}

