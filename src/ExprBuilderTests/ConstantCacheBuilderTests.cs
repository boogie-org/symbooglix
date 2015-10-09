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
using System.Numerics;
using Microsoft.Basetypes;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class ConstantCacheBuilderTests : SimpleExprBuilderTestBase
    {
        [Test()]
        public void testBoolean()
        {
            var ccB = new ConstantCachingExprBuilder(this.GetSimpleBuilder());

            var trueExpr = ccB.True;
            Assert.IsTrue(trueExpr.isBool && trueExpr.asBool);
            var falseExpr = ccB.False;
            Assert.IsTrue(falseExpr.isBool && !falseExpr.asBool);

            Assert.AreSame(trueExpr, ccB.True);
            Assert.AreSame(falseExpr, ccB.False);

            // Test other interface
            Assert.AreSame(trueExpr, ccB.ConstantBool(true));
            Assert.AreSame(falseExpr, ccB.ConstantBool(false));
        }

        [TestCase(true)]
        [TestCase(false)]
        public void testBv(bool useIntInterface)
        {
            var ccB = new ConstantCachingExprBuilder(this.GetSimpleBuilder());

            for (int bitWidth = 1; bitWidth < 16; ++bitWidth)
            {
                for (int value = 0; value < (1 << bitWidth); ++value)
                {
                    var bvExpr = useIntInterface ? ccB.ConstantBV(value, bitWidth) : ccB.ConstantBV(new BigInteger(value), bitWidth);
                    var bvExpr2 = useIntInterface ? ccB.ConstantBV(value, bitWidth) : ccB.ConstantBV(new BigInteger(value), bitWidth);
                    Assert.AreSame(bvExpr, bvExpr2);
                }
            }
        }

        [TestCase(true)]
        [TestCase(false)]
        public void testInt(bool useIntInterface)
        {
            var ccB = new ConstantCachingExprBuilder(this.GetSimpleBuilder());

            for (int value = -1000; value < 1000; ++value)
            {
                var intExpr = useIntInterface ? ccB.ConstantInt(value) : ccB.ConstantInt(new BigInteger(value));
                var intExpr2 = useIntInterface ? ccB.ConstantInt(value) : ccB.ConstantInt(new BigInteger(value));
                Assert.AreSame(intExpr, intExpr2);
            }
        }

        [TestCase(true)]
        [TestCase(false)]
        public void testReal(bool useStringInterface)
        {
            var ccB = new ConstantCachingExprBuilder(this.GetSimpleBuilder());

            for (BigDec value = BigDec.FromInt(-20); value <= BigDec.FromInt(20); value += BigDec.FromString("0.1"))
            {
                var asString = value.ToString();
                var realExpr = useStringInterface ? ccB.ConstantReal(asString) : ccB.ConstantReal(value);
                var realExpr2 = useStringInterface ? ccB.ConstantReal(asString) : ccB.ConstantReal(value);
                Assert.AreSame(realExpr, realExpr2);
            }
        }

    }
}

