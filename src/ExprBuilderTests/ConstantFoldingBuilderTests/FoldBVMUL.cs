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
    public class FoldBVMUL : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 0, 2, 0)]
        [TestCase(5, 2, 8, 10)] // Positive no overflow
        [TestCase(5, 5, 4, 9)] // Positive overflow
        [TestCase(-2, 3, 4, 10)] // Negative no underflow
        [TestCase(-2, 5, 4, 6)] // Negative underflow
        public void simpleAdd(int lhsValue, int rhsValue, int bitWidth, int expectedValue)
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.BVMUL(cfb.ConstantBV(lhsValue, bitWidth), cfb.ConstantBV(rhsValue, bitWidth));
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
            var simpleResult = sfb.BVMUL(arg0, arg1);
            var result = cfb.BVMUL(arg0, arg1);
            CheckIsBvType(simpleResult, 8);
            CheckIsBvType(result, 8);
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsBVMUL(result));
            Assert.IsTrue(ExprUtil.StructurallyEqual(result, simpleResult));
        }

        // 0 * x ==> x
        [Test()]
        public void mulByLhsZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVMUL(cfb.ConstantBV(0, 8), x);
            CheckIsBvType(result, 8);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(ExprUtil.IsZero(asLit));
        }

        // x * 0 ==> x
        [Test()]
        public void mulByRhsZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVMUL(x, cfb.ConstantBV(0, 8));
            CheckIsBvType(result, 8);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(ExprUtil.IsZero(asLit));
        }

        [Test()]
        public void MulAssociativityPropagateConstantUp()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            Expr foldedResult = sb.ConstantBV(1, 8);
            Expr unfoldedResult = foldedResult;

            for (int index = 0; index < 3; ++index)
            {
                var x = GetVarAndIdExpr("x" + index.ToString(), BasicType.GetBvType(8)).Item2;
                foldedResult = cfb.BVMUL(x, foldedResult);
                unfoldedResult = sb.BVMUL(x, unfoldedResult);
                CheckIsBvType(foldedResult, 8);
                CheckIsBvType(unfoldedResult, 8);
            }
            Assert.AreEqual("BVMUL8(1bv8, BVMUL8(x2, BVMUL8(x1, x0)))", foldedResult.ToString());
            Assert.AreEqual("BVMUL8(x2, BVMUL8(x1, BVMUL8(x0, 1bv8)))", unfoldedResult.ToString());
            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            var foldedTopAsNAry = ExprUtil.AsBVMUL(foldedResult);
            // Check the constant is the top left argument
            var topLeftConstant = ExprUtil.AsLiteral(foldedTopAsNAry.Args[0]);
            Assert.IsNotNull(topLeftConstant);
            CheckIsBvType(topLeftConstant, 8);
            Assert.AreEqual(1, topLeftConstant.asBvConst.Value.ToInt);

        }

        [Test()]
        public void MULAssociativityAddNearbyConstants()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            var x = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;

            Expr foldedResult = x;
            Expr unfoldedResult = foldedResult;

            for (int index = 2; index <= 4; ++index)
            {
                foldedResult = cfb.BVMUL(cfb.ConstantBV(index, 8), foldedResult);
                unfoldedResult = sb.BVMUL(sb.ConstantBV(index, 8), unfoldedResult);
                CheckIsBvType(foldedResult, 8);
                CheckIsBvType(unfoldedResult, 8);
            }
            Assert.AreEqual("BVMUL8(24bv8, x)", foldedResult.ToString());
            Assert.AreEqual("BVMUL8(4bv8, BVMUL8(3bv8, BVMUL8(2bv8, x)))", unfoldedResult.ToString());
            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            var foldedTopAsNAry = ExprUtil.AsBVMUL(foldedResult);
            // Check the constant is the top left argument
            var topLeftConstant = ExprUtil.AsLiteral(foldedTopAsNAry.Args[0]);
            Assert.IsNotNull(topLeftConstant);
            CheckIsBvType(topLeftConstant, 8);
            Assert.AreEqual(24, topLeftConstant.asBvConst.Value.ToInt);
        }
    }
}

