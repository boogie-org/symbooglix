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
    public class FoldBVADD : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 0, 2, 0)]
        [TestCase(1, 1, 2, 2)]
        [TestCase(1, 2, 2, 3)]
        [TestCase(2, 2, 2, 0)]
        [TestCase(4, 6, 4, 10)]
        [TestCase(15, 0, 4, 15)]
        [TestCase(15, 1, 4, 0)]
        public void simpleAdd(int lhsValue, int rhsValue, int bitWidth, int expectedValue)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.BVADD(cfb.ConstantBV(lhsValue, bitWidth), cfb.ConstantBV(rhsValue, bitWidth));
            CheckIsBvType(result, bitWidth);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.AreEqual(expectedValue, asLit.asBvConst.Value.ToInt);
        }

        [Test()]
        public void NoFold()
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            SimpleExprBuilder sfb = builders.Item1;
            ConstantFoldingExprBuilder cfb = builders.Item2;
            var arg0 = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var arg1 = GetVarAndIdExpr("y", BasicType.GetBvType(8)).Item2;
            var simpleResult = sfb.BVADD(arg0, arg1);
            var result = cfb.BVADD(arg0, arg1);
            CheckIsBvType(result, 8);
            CheckIsBvType(simpleResult, 8);
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsBVADD(result));
            Assert.IsTrue(ExprUtil.StructurallyEqual(result, simpleResult));
        }

        // 0 + x ==> x
        [Test()]
        public void lhsIsZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVADD(cfb.ConstantBV(0, 8), x);
            CheckIsBvType(result, 8);
            Assert.AreSame(x, result);
        }

        // x + 0 ==> x
        [Test()]
        public void rhsIsZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVADD(x, cfb.ConstantBV(0, 8));
            CheckIsBvType(result, 8);
            Assert.AreSame(x, result);
        }

        // <expr> + <expr> ==> 2 * <expr>
        [Test()]
        public void SameExprAdded()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var y = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var side = cfb.BVADD(x, y);
            CheckIsBvType(side, 8);
            Assert.IsNull(ExprUtil.AsLiteral(side));
            var result = cfb.BVADD(side, side);
            CheckIsBvType(result, 8);
            var mul = ExprUtil.AsBVMUL(result);
            Assert.IsNotNull(mul);
            var lhs = ExprUtil.AsLiteral(mul.Args[0]);
            Assert.IsNotNull(lhs);
            Assert.AreEqual(2, lhs.asBvConst.Value.ToInt);
            Assert.AreSame(side, mul.Args[1]);
        }

        [Test()]
        public void AddAssociativityPropagateConstantUp()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            Expr foldedResult = sb.ConstantBV(1, 8);
            Expr unfoldedResult = foldedResult;

            for (int index = 0; index < 3; ++index)
            {
                var x = GetVarAndIdExpr("x" + index.ToString(), BasicType.GetBvType(8)).Item2;
                foldedResult = cfb.BVADD(x, foldedResult);
                unfoldedResult = sb.BVADD(x, unfoldedResult);
                CheckIsBvType(foldedResult, 8);
                CheckIsBvType(unfoldedResult, 8);
            }
            Assert.AreEqual("BVADD8(1bv8, BVADD8(x2, BVADD8(x1, x0)))", foldedResult.ToString());
            Assert.AreEqual("BVADD8(x2, BVADD8(x1, BVADD8(x0, 1bv8)))", unfoldedResult.ToString());
            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            var foldedTopAsNAry = ExprUtil.AsBVADD(foldedResult);
            // Check the constant is the top left argument
            var topLeftConstant = ExprUtil.AsLiteral(foldedTopAsNAry.Args[0]);
            Assert.IsNotNull(topLeftConstant);
            CheckIsBvType(topLeftConstant, 8);
            Assert.AreEqual(1, topLeftConstant.asBvConst.Value.ToInt);

        }

        [Test()]
        public void AddAssociativityAddNearbyConstants()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            var x = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;

            Expr foldedResult = x;
            Expr unfoldedResult = foldedResult;

            for (int index = 1; index <= 3; ++index)
            {
                foldedResult = cfb.BVADD(cfb.ConstantBV(index, 8), foldedResult);
                unfoldedResult = sb.BVADD(sb.ConstantBV(index, 8), unfoldedResult);
                CheckIsBvType(foldedResult, 8);
                CheckIsBvType(unfoldedResult, 8);
            }
            Assert.AreEqual("BVADD8(6bv8, x)", foldedResult.ToString());
            Assert.AreEqual("BVADD8(3bv8, BVADD8(2bv8, BVADD8(1bv8, x)))", unfoldedResult.ToString());
            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            var foldedTopAsNAry = ExprUtil.AsBVADD(foldedResult);
            // Check the constant is the top left argument
            var topLeftConstant = ExprUtil.AsLiteral(foldedTopAsNAry.Args[0]);
            Assert.IsNotNull(topLeftConstant);
            CheckIsBvType(topLeftConstant, 8);
            Assert.AreEqual(6, topLeftConstant.asBvConst.Value.ToInt);
        }
    }
}

