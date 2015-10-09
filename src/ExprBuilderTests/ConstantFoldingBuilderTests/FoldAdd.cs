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
    public class FoldAdd : ConstantFoldingExprBuilderTests
    {
        [TestCase(5, 3, 8)]
        [TestCase(3, 5, 8)]
        [TestCase(3, 0, 3)]
        [TestCase(0, 3, 3)]
        [TestCase(0, 0, 0)]
        public void AddSimpleConstantsInt(int lhs, int rhs, int expectedValue)
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Add(cfb.ConstantInt(lhs), cfb.ConstantInt(rhs));
            CheckIsInt(result);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsTrue(asLit.isBigNum);
            Assert.AreEqual(BigNum.FromInt(expectedValue), asLit.asBigNum);
        }

        [Test()]
        public void AddZeroToExprInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Add(x, cfb.ConstantInt(0));
            CheckIsInt(result);
            Assert.AreSame(x, result);
        }

        [Test()]
        public void AddZeroToExprReal()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Add(x, cfb.ConstantReal("0.0"));
            CheckIsReal(result);
            Assert.AreSame(x, result);
        }

        [TestCase("5.0", "3.0", "8e0")]
        [TestCase("3.0", "5.0", "8e0")]
        [TestCase("5.5", "3.0", "8.5e0")]
        [TestCase("3.0", "5.5", "8.5e0")]
        public void AddSimpleConstantsReal(string lhs, string rhs, string expectedValue)
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Add(cfb.ConstantReal(lhs), cfb.ConstantReal(rhs));
            CheckIsReal(result);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsTrue(asLit.isBigDec);
        }

        [Test()]
        public void AddSameIntVars()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var result = cfb.Add(x, x);
            CheckIsInt(result);
            var asMul = ExprUtil.AsMul(result);
            Assert.IsNotNull(asMul);
            var asMulLhs = ExprUtil.AsLiteral(asMul.Args[0]);
            Assert.IsNotNull(asMulLhs);
            Assert.AreEqual(BigNum.FromInt(2), asMulLhs.asBigNum);
            Assert.AreSame(x, asMul.Args[1]);
            Assert.AreEqual("2 * x", result.ToString());
        }

        [Test()]
        public void AddSimpleConstantsRealVars()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var result = cfb.Add(x, x);
            CheckIsReal(result);
            var asMul = ExprUtil.AsMul(result);
            Assert.IsNotNull(asMul);
            var asMulLhs = ExprUtil.AsLiteral(asMul.Args[0]);
            Assert.IsNotNull(asMulLhs);
            Assert.AreEqual("2e0", asMulLhs.asBigDec.ToString());
            Assert.AreSame(x, asMul.Args[1]);
            Assert.AreEqual("2e0 * x", result.ToString());
        }

        [Test()]
        public void AddAssociativityPropagateConstantUp()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            Expr foldedResult = sb.ConstantInt(1);
            Expr unfoldedResult = foldedResult;

            for (int index = 0; index < 3; ++index)
            {
                var x = GetVarAndIdExpr("x" + index.ToString(), BasicType.Int).Item2;
                foldedResult = cfb.Add(x, foldedResult);
                unfoldedResult = sb.Add(x, unfoldedResult);
                CheckIsInt(foldedResult);
                CheckIsInt(unfoldedResult);
            }
            Assert.AreEqual("1 + x2 + x1 + x0", foldedResult.ToString());
            Assert.AreEqual("x2 + x1 + x0 + 1", unfoldedResult.ToString());
            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            var topAsAdd = ExprUtil.AsAdd(foldedResult);
            Assert.IsNotNull(topAsAdd);
            var topLhsAsLit = ExprUtil.AsLiteral(topAsAdd.Args[0]);
            Assert.IsNotNull(topLhsAsLit);
            Assert.AreEqual(BigNum.FromInt(1), topLhsAsLit.asBigNum);
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

            for (int index = 1; index <= 3; ++index)
            {
                foldedResult = cfb.Add(cfb.ConstantInt(index), foldedResult);
                unfoldedResult = sb.Add(sb.ConstantInt(index), unfoldedResult);
            }
            Assert.AreEqual("6 + x", foldedResult.ToString());
            Assert.AreEqual("3 + 2 + 1 + x", unfoldedResult.ToString());
            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            var topAsAdd = ExprUtil.AsAdd(foldedResult);
            Assert.IsNotNull(topAsAdd);
            var topLhsAsLit = ExprUtil.AsLiteral(topAsAdd.Args[0]);
            Assert.IsNotNull(topLhsAsLit);
            Assert.AreEqual(BigNum.FromInt(6), topLhsAsLit.asBigNum);
        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var v1 = GetVarAndIdExpr("y", BasicType.Int);
            var foldedResult = cfb.Add(v0.Item2, v1.Item2);
            var simpleResult = sfb.Add(v0.Item2, v1.Item2);
            CheckIsInt(foldedResult);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

