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
    public class FoldSub : ConstantFoldingExprBuilderTests
    {
        [TestCase(5,3,2)]
        [TestCase(5,5,0)]
        [TestCase(5,6,-1)]
        public void SubSimpleConstantsInt(int lhs, int rhs, int expectedValue)
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Sub(cfb.ConstantInt(lhs), cfb.ConstantInt(rhs));
            CheckIsInt(result);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.AreEqual(BigNum.FromInt(expectedValue), asLit.asBigNum);
        }

        [TestCase("5.0", "3.0", "2e0")]
        [TestCase("5.1", "3.0", "21e-1")]
        public void SubSimpleConstantsReal(string lhs, string rhs, string expectedValue)
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Sub(cfb.ConstantReal(lhs), cfb.ConstantReal(rhs));
            CheckIsReal(result);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.AreEqual(expectedValue, asLit.asBigDec.ToString());
        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var v1 = GetVarAndIdExpr("y", BasicType.Int);
            var foldedResult = cfb.Sub(v0.Item2, v1.Item2);
            var simpleResult = sfb.Sub(v0.Item2, v1.Item2);
            CheckIsInt(foldedResult);
            CheckIsInt(simpleResult);
            Assert.AreEqual(simpleResult, foldedResult);
        }

        // 0 - <expr> ==> -<expr>
        [Test()]
        public void LhsIntZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var result = cfb.Sub(cfb.ConstantInt(0), x);
            CheckIsInt(result);
            var asNeg = ExprUtil.AsNeg(result);
            Assert.IsNotNull(asNeg);
            Assert.AreSame(x, asNeg.Args[0]);
        }

        // 0 - <expr> ==> -<expr>
        [Test()]
        public void LhsRealZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var result = cfb.Sub(cfb.ConstantReal("0.0"), x);
            CheckIsReal(result);
            var asNeg = ExprUtil.AsNeg(result);
            Assert.IsNotNull(asNeg);
            Assert.AreSame(x, asNeg.Args[0]);
        }

        // <expr> - 0 ==> <expr>
        [Test()]
        public void RhsIntZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var result = cfb.Sub(x, cfb.ConstantInt(0));
            CheckIsInt(result);
            Assert.AreSame(x, result);
        }

        [Test()]
        public void RhsRealZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var result = cfb.Sub(x, cfb.ConstantReal("0.0"));
            CheckIsReal(result);
            Assert.AreSame(x, result);
        }

        // <expr> - <constant>  ==> (-<constant>) + <expr>
        [Test()]
        public void MinusConstantIntToAdd()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var constant = cfb.ConstantInt(2);
            var result = cfb.Sub(x, constant);
            CheckIsInt(result);
            var asAdd = ExprUtil.AsAdd(result);
            Assert.IsNotNull(asAdd);
            var lhs = ExprUtil.AsLiteral(asAdd.Args[0]);
            Assert.IsNotNull(lhs);
            Assert.AreEqual(-2, lhs.asBigNum.ToInt);
        }

        // <expr> - <constant>  ==> (-<constant>) + <expr>
        [Test()]
        public void MinusConstantRealToAdd()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var constant = cfb.ConstantReal("2.0");
            var result = cfb.Sub(x, constant);
            CheckIsReal(result);
            var asAdd = ExprUtil.AsAdd(result);
            Assert.IsNotNull(asAdd);
            var lhs = ExprUtil.AsLiteral(asAdd.Args[0]);
            Assert.IsNotNull(lhs);
            Assert.AreEqual("-2e0", lhs.asBigDec.ToString());
        }
 
        // <expr> - <expr> ==> 0
        [Test()]
        public void SubtractIdenticalIntExpr()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var y = GetVarAndIdExpr("y", BasicType.Int).Item2;
            var side = cfb.Add(x, y);
            var result = cfb.Sub(side, side);
            var asLit = ExprUtil.AsLiteral(result);
            CheckIsInt(result);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(asLit.asBigNum.IsZero);
        }

        [Test()]
        public void SubtractIdenticalRealExpr()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var y = GetVarAndIdExpr("y", BasicType.Real).Item2;
            var side = cfb.Add(x, y);
            var result = cfb.Sub(side, side);
            var asLit = ExprUtil.AsLiteral(result);
            CheckIsReal(result);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(asLit.asBigDec.IsZero);
        }
    }
}

