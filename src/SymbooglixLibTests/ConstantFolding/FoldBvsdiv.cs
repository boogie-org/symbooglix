﻿using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Symbooglix;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBvsdiv : TestBase
    {
        [Test()]
        public void PositiveNumeratorPositiveDenominator()
        {
            var arg0 = builder.ConstantBV(7, 4);
            var arg1 = builder.ConstantBV(2, 4);
            helper(arg0, arg1, 3);
        }

        [Test()]
        public void PositiveNumeratorNegativeDenominator()
        {
            var arg0 = builder.ConstantBV(7, 4);
            var arg1 = builder.ConstantBV(-2, 4);
            helper(arg0, arg1, -3);
        }

        [Test()]
        public void NegativeNumeratorPositiveDenominator()
        {
            var arg0 = builder.ConstantBV(-7, 4);
            var arg1 = builder.ConstantBV(2, 4);
            helper(arg0, arg1, -3);
        }

        [Test()]
        public void NegativeNumeratorNegativeDenominator()
        {
            var arg0 = builder.ConstantBV(-7, 4);
            var arg1 = builder.ConstantBV(-2, 4);
            helper(arg0, arg1, 3);
        }

        [Test(),ExpectedException(typeof(DivideByZeroException))]
        public void DivisionByZero()
        {
            var arg0 = builder.ConstantBV(-7, 4);
            var arg1 = builder.ConstantBV(0, 4);
            helper(arg0, arg1, 0);
        }

        private Expr helper(Expr arg0, Expr arg1, int expected)
        {
            var sdiv = builder.BVSDIV(arg0, arg1);

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(sdiv);
            Assert.IsInstanceOfType(typeof(LiteralExpr), result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(builder.ConstantBV(expected, 4).asBvConst.Value, ( result as LiteralExpr ).asBvConst.Value);
            return result;
        }
    }
}
