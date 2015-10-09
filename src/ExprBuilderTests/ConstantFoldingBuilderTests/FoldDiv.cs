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
    public class FoldDiv : ConstantFoldingExprBuilderTests
    {
        // m div n = q
        // m mod n = r
        // nq + r = m
        // 0 <= r <= ( |n| =-1 )
        [TestCase(8, 2, 4)]
        [TestCase(8, 3, 2)]
        [TestCase(1, -4, 0)] // check round towards zero
        [TestCase(11, 3, 3)] // q = 3 , r=2
        [TestCase(11, -3, -3)] // q = -3, r=2
        [TestCase(-11, 3, -4)] // q = -4, r =1
        [TestCase(-11, -3, 4)] // q = 4, r=1
        public void DivideSimpleConstantsInt(int numerator, int denomiator, int expectedValue)
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Div(cfb.ConstantInt(numerator), cfb.ConstantInt(denomiator));
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            CheckIsInt(result);
            Assert.AreEqual(BigNum.FromInt(expectedValue), asLit.asBigNum);
        }

        [Test()]
        public void DivideByZero()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Div(cfb.ConstantInt(8), cfb.ConstantInt(0));
            CheckIsInt(result);
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsDiv(result));
            Assert.AreEqual("8 div 0", result.ToString());
        }

        [Test()]
        public void DivideByOneInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Div(x, cfb.ConstantInt(1));
            CheckIsInt(result);
            Assert.AreSame(x, result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void DivideByOneReal()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var cfb = builderPair.Item2;
            cfb.Div(x, cfb.ConstantReal("1.0"));
        }

        [Test()]
        public void ZeroDivideByIntExpr()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Div(cfb.ConstantInt(0), x);
            CheckIsInt(result);
            Assert.IsFalse(ExprUtil.IsZero(result));
            Assert.IsNotNull(ExprUtil.AsDiv(result));
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void ZeroDivideByRealExpr()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var cfb = builderPair.Item2;
            cfb.Div(cfb.ConstantReal("0.0"), x);
        }

        [Test()]
        public void NestedDivInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var y = GetVarAndIdExpr("y", BasicType.Int).Item2;
            var z = GetVarAndIdExpr("z", BasicType.Int).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Div(cfb.Div(x, y), z);
            var asDiv = ExprUtil.AsDiv(result);
            Assert.IsNotNull(asDiv);
            CheckIsInt(result);
            Assert.AreSame(x, asDiv.Args[0]);
            var rhsOfDiv = ExprUtil.AsMul(asDiv.Args[1]);
            Assert.IsNotNull(rhsOfDiv);
            Assert.AreSame(y, rhsOfDiv.Args[0]);
            Assert.AreSame(z, rhsOfDiv.Args[1]);

        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var v1 = GetVarAndIdExpr("y", BasicType.Int);
            var foldedResult = cfb.Div(v0.Item2, v1.Item2);
            var simpleResult = sfb.Div(v0.Item2, v1.Item2);
            CheckIsInt(foldedResult);
            CheckIsInt(simpleResult);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

