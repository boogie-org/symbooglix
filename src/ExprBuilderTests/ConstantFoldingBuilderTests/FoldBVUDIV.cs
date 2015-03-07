using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBVUDIV : ConstantFoldingExprBuilderTests
    {
        [TestCase(0, 5, 4, 0)]
        [TestCase(1, 1, 2, 1)]
        [TestCase(8, 4, 4, 2)]
        [TestCase(10, 7, 4, 1)]
        [TestCase(1, 4, 4, 0)]
        [TestCase(2, 4, 4, 0)]
        [TestCase(3, 4, 4, 0)]
        [TestCase(4, 4, 4, 1)]
        [TestCase(5, 4, 4, 1)]
        [TestCase(6, 4, 4, 1)]
        [TestCase(7, 4, 4, 1)]
        [TestCase(8, 4, 4, 2)]
        [TestCase(9, 4, 4, 2)]
        [TestCase(10, 4, 4, 2)]
        [TestCase(11, 4, 4, 2)]
        [TestCase(12, 4, 4, 3)]
        [TestCase(13, 4, 4, 3)]
        [TestCase(14, 4, 4, 3)]
        [TestCase(15, 4, 4, 3)]
        public void SimpleConstants(int dividendValue, int divisorValue, int bitWidth, int expectedValue)
        {
            var cfb = GetConstantFoldingBuilder();
            var dividend = cfb.ConstantBV(dividendValue, bitWidth);
            var divisor = cfb.ConstantBV(divisorValue, bitWidth);
            var result = cfb.BVUDIV(dividend, divisor);
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            CheckIsBvType(result, bitWidth);
            Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(expectedValue), asLit.asBvConst.Value);
        }

        [Test()]
        public void DivideByZero()
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            var sfb = builders.Item1;
            var cfb = builders.Item2;
            var dividend = cfb.ConstantBV(5, 4);
            var divisor = cfb.ConstantBV(0, 4);

            var noFoldResult = sfb.BVUDIV(dividend, divisor);
            var cfbNoFold = cfb.BVUDIV(dividend, divisor);
            Assert.IsNull(ExprUtil.AsLiteral(cfbNoFold));
            Assert.IsTrue(ExprUtil.StructurallyEqual(noFoldResult, cfbNoFold));
            CheckIsBvType(cfbNoFold, 4);
        }

        [Test()]
        public void NoFold()
        {
            var cfb = GetConstantFoldingBuilder();
            var dividend = GetVarAndIdExpr("x", BasicType.GetBvType(8)).Item2;
            var divisor = GetVarAndIdExpr("y", BasicType.GetBvType(8)).Item2;
            var result = cfb.BVUDIV(dividend, divisor);
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsBVUDIV(result));
        }
    }
}

