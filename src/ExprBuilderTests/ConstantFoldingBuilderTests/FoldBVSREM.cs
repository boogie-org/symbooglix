using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBVSREM : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 5, 4, 0)]
        [TestCase(1, 1, 1, 0)]
        [TestCase(10, 7, 4, 10)]
        [TestCase(1, 4, 4, 1)]
        [TestCase(2, 4, 4, 2)]
        [TestCase(3, 4, 4, 3)]
        [TestCase(4, 4, 4, 0)]
        [TestCase(5, 4, 4, 1)]
        [TestCase(6, 4, 4, 2)]
        [TestCase(7, 4, 4, 3)]
        [TestCase(8, 4, 4, 0)]
        [TestCase(9, 4, 4, 13)]
        [TestCase(10, 4, 4, 14)]
        [TestCase(11, 4, 4, 15)]
        [TestCase(12, 4, 4, 0)]
        [TestCase(13, 4, 4, 13)]
        [TestCase(14, 4, 4, 14)]
        [TestCase(15, 4, 4, 15)]
        public void SimpleConstants(int dividendValue, int divisorValue, int bitWidth, int expectedValue)
        {
            var cfb = GetConstantFoldingBuilder();
            var dividend = cfb.ConstantBV(dividendValue, bitWidth);
            var divisor = cfb.ConstantBV(divisorValue, bitWidth);
            var result = cfb.BVSREM(dividend, divisor);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            CheckIsBvType(result, bitWidth);
            Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(expectedValue), asLit.asBvConst.Value);
        }

        [Test()]
        public void RemByZero()
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            var sfb = builders.Item1;
            var cfb = builders.Item2;
            var dividend = cfb.ConstantBV(5, 4);
            var divisor = cfb.ConstantBV(0, 4);

            var noFoldResult = sfb.BVSREM(dividend, divisor);
            var cfbNoFold = cfb.BVSREM(dividend, divisor);
            Assert.IsNull(ExprUtil.AsLiteral(cfbNoFold));
            Assert.IsTrue(ExprUtil.StructurallyEqual(noFoldResult, cfbNoFold));
            CheckIsBvType(cfbNoFold, 4);
        }

        [Test()]
        public void RemByOne()
        {
            var cfb = GetConstantFoldingBuilder();
            var dividend = GetVarAndIdExpr("x", BasicType.GetBvType(4)).Item2;
            var divisor = cfb.ConstantBV(1, 4);
            var result = cfb.BVSREM(dividend, divisor);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            CheckIsBvType(result, 4);
            Assert.IsTrue(ExprUtil.IsZero(result));
        }

        [Test()]
        public void NoFold()
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            SimpleExprBuilder sfb = builders.Item1;
            ConstantFoldingExprBuilder cfb = builders.Item2;
            var arg0 = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var arg1 = GetVarAndIdExpr("y", BasicType.GetBvType(8)).Item2;
            var simpleResult = sfb.BVSREM(arg0, arg1);
            var result = cfb.BVSREM(arg0, arg1);
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsBVSREM(result));
            Assert.IsTrue(ExprUtil.StructurallyEqual(result, simpleResult));
        }
    }
}

