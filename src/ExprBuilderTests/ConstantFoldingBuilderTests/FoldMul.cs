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
    public class FoldMul : ConstantFoldingExprBuilderTests
    {
        [TestCase(5, 3, 15)]
        [TestCase(3, 5, 15)]
        [TestCase(1, 5, 5)]
        [TestCase(-1, 5, -5)]
        public void MulSimpleConstantsInt(int lhs, int rhs, int expectedValue)
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Mul(cfb.ConstantInt(lhs), cfb.ConstantInt(rhs));
            CheckIsInt(result);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.AreEqual(BigNum.FromInt(expectedValue), asLit.asBigNum);
        }

        [Test()]
        public void MulByZeroExprInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Mul(x, cfb.ConstantInt(0));
            CheckIsInt(result);
            Assert.AreEqual("0", result.ToString());
            var lit = ExprUtil.AsLiteral(result);
            Assert.AreEqual(0, lit.asBigNum.ToInt);
        }

        [Test()]
        public void MulByOneToExprInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Mul(x, cfb.ConstantInt(1));
            CheckIsInt(result);
            Assert.AreSame(x, result);
        }

        [Test()]
        public void MulByZeroExprReal()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Mul(x, cfb.ConstantReal("0.0"));
            CheckIsReal(result);
            var lit = ExprUtil.AsLiteral(result);
            Assert.IsTrue(lit.asBigDec.IsZero);
        }

        [Test()]
        public void MulByOneToExprReal()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Mul(x, cfb.ConstantReal("1.0"));
            CheckIsReal(result);
            Assert.AreSame(x, result);
        }

        [TestCase("5.0", "3.0", "15e0")]
        [TestCase("-5.0", "3.0", "-15e0")]
        [TestCase("-5.0", "-3.0", "15e0")]
        [TestCase("5.0", "-3.0", "-15e0")]
        public void MulSimpleConstantsReal(string lhs, string rhs, string expectedValue)
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Mul(cfb.ConstantReal(lhs), cfb.ConstantReal(rhs));
            CheckIsReal(result);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.AreEqual(expectedValue, asLit.asBigDec.ToString());
        }



        [Test()]
        public void MulAssociativityPropagateConstantUp()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            Expr foldedResult = sb.ConstantInt(2);
            Expr unfoldedResult = foldedResult;

            for (int index = 0; index < 3; ++index)
            {
                var x = GetVarAndIdExpr("x" + index.ToString(), BasicType.Int).Item2;
                foldedResult = cfb.Mul(x, foldedResult);
                unfoldedResult = sb.Mul(x, unfoldedResult);
                CheckIsInt(foldedResult);
                CheckIsInt(unfoldedResult);
            }
            Assert.AreEqual("2 * x2 * x1 * x0", foldedResult.ToString());
            Assert.AreEqual("x2 * x1 * x0 * 2", unfoldedResult.ToString());
            Assert.IsFalse(foldedResult.Equals(unfoldedResult));


            var asMul = ExprUtil.AsMul(foldedResult);
            Assert.IsNotNull(asMul);
            // Check the constant is the top left argument
            Assert.IsNotNull(ExprUtil.AsLiteral(asMul.Args[0]));
        }


        [Test()]
        public void AddAssociativityAddNearbyConstants()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;

            Expr foldedResult = x;
            Expr unfoldedResult = foldedResult;

            for (int index = 2; index <= 4; ++index)
            {
                foldedResult = cfb.Mul(cfb.ConstantInt(index), foldedResult);
                unfoldedResult = sb.Mul(sb.ConstantInt(index), unfoldedResult);
                CheckIsInt(foldedResult);
                CheckIsInt(unfoldedResult);
            }
            Assert.AreEqual("24 * x", foldedResult.ToString());
            Assert.AreEqual("4 * 3 * 2 * x", unfoldedResult.ToString());
            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            var asMul = ExprUtil.AsMul(foldedResult);
            Assert.IsNotNull(asMul);
            // Check the constant is the top left argument
            Assert.IsNotNull(ExprUtil.AsLiteral(asMul.Args[0]));
        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var v1 = GetVarAndIdExpr("y", BasicType.Int);
            var foldedResult = cfb.Mul(v0.Item2, v1.Item2);
            var simpleResult = sfb.Mul(v0.Item2, v1.Item2);
            CheckIsInt(foldedResult);
            CheckIsInt(simpleResult);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

