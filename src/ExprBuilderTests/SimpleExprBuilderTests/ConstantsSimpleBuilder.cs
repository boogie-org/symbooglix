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
using Symbooglix;
using Microsoft.Basetypes;
using Microsoft.Boogie;
using System.Numerics;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class ConstantsSimpleBuilder : SimpleExprBuilderTestBase
    {
        [Test()]
        public void True()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.True;
            Assert.AreEqual("true", constant.ToString());
            CheckType(constant, t => t.IsBool);

            var constant2 = builder.ConstantBool(true);
            Assert.AreEqual("true", constant2.ToString());
            CheckType(constant2, t => t.IsBool);
        }

        [Test()]
        public void False()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.False;
            Assert.AreEqual("false", constant.ToString());
            CheckType(constant, t => t.IsBool);

            var constant2 = builder.ConstantBool(false);
            Assert.AreEqual("false", constant2.ToString());
            CheckType(constant, t => t.IsBool);
        }

        [Test()]
        public void PositiveInteger()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantInt(5);
            Assert.AreEqual("5", constant.ToString());
            Assert.AreEqual(5, constant.asBigNum.ToInt);
            CheckType(constant, t => t.IsInt);
        }

        [Test()]
        public void PositiveIntegerFromBigInt()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantInt(new BigInteger(5));
            Assert.AreEqual("5", constant.ToString());
            Assert.AreEqual(5, constant.asBigNum.ToInt);
            CheckType(constant, t => t.IsInt);
        }

        [Test()]
        public void NegativeInteger()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantInt(-5);
            Assert.AreEqual("-5", constant.ToString());
            Assert.AreEqual(-5, constant.asBigNum.ToInt);
            CheckType(constant, t => t.IsInt);
        }

        [Test()]
        public void NegativeIntegerFromBigInt()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantInt( new BigInteger(-5));
            Assert.AreEqual("-5", constant.ToString());
            Assert.AreEqual(-5, constant.asBigNum.ToInt);
            CheckType(constant, t => t.IsInt);
        }

        [Test()]
        public void PositiveReal()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantReal("5.0");
            Assert.AreEqual("5e0", constant.ToString());
            CheckType(constant, t => t.IsReal);
        }

        [Test()]
        public void PositiveRealFromBigDec()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantReal(BigDec.FromInt(5));
            Assert.AreEqual("5e0", constant.ToString());
            CheckType(constant, t => t.IsReal);
        }

        [Test()]
        public void NegativeReal()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantReal("-5.0");
            Assert.AreEqual("-5e0", constant.ToString());
            CheckType(constant, t => t.IsReal);
        }

        [Test()]
        public void NegativeRealFromBigDec()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantReal(BigDec.FromInt(-5));
            Assert.AreEqual("-5e0", constant.ToString());
            CheckType(constant, t => t.IsReal);
        }

        [TestCase(5, 4, "5bv4")]
        [TestCase(11, 32, "11bv32")]
        [TestCase(0, 4, "0bv4")]
        [TestCase (15, 4, "15bv4")]
        public void PositiveBV(int decimalValue, int width, string expectedString)
        {
            _PositiveBV(decimalValue, width, expectedString);
        }

        [TestCase(16, 4)]
        [TestCase(20, 2)]
        [TestCase(256, 8)]
        [TestCase(311, 8)]
        [ExpectedException(typeof(ArgumentException))]
        public void PositiveBVOutOfRange(int decimalValue, int width)
        {
            _PositiveBV(decimalValue, width, "dummy");
        }

        private void _PositiveBV(int decimalValue, int width, string expectedString)
        {
            Assert.IsTrue(decimalValue >= 0);
            var builder = GetSimpleBuilder();
            // Test both versions of the API
            var constants = new Microsoft.Boogie.LiteralExpr[] {
                builder.ConstantBV(decimalValue, width),
                builder.ConstantBV(new BigInteger(decimalValue), width)};

            foreach (var constant in constants)
            {
                Assert.AreEqual(expectedString, constant.ToString());
                CheckType(constant, t => t.IsBv);
                Assert.AreEqual(width, constant.asBvConst.Bits);
                Assert.AreEqual(width, constant.Type.BvBits);
                Assert.AreEqual(decimalValue, constant.asBvConst.Value.ToInt);
            }
        }

        [TestCase(-5, 4, "11bv4")]
        [TestCase(-11, 32, "4294967285bv32")]
        [TestCase(0, 4, "0bv4")]
        [TestCase(-8, 4, "8bv4")]
        public void NegativeBV(int decimalValue, int width, string expectedString)
        {
            _NegativeBV(decimalValue, width, expectedString);
        }

        [TestCase(-9, 4)]
        [TestCase(-3, 2)]
        [TestCase(-129, 8)]
        [TestCase(-200, 8)]
        [ExpectedException(typeof(ArgumentException))]
        public void NegativeBVOutOfRange(int decimalValue, int width)
        {
            _NegativeBV(decimalValue, width, "dummy");
        }

        public void _NegativeBV(int decimalValue, int width, string expectedString)
        {
            Assert.IsTrue(decimalValue <= 0);
            var builder = GetSimpleBuilder();
            // Test both versions of the API
            var constants = new Microsoft.Boogie.LiteralExpr[] {
                builder.ConstantBV(decimalValue, width),
                builder.ConstantBV(new BigInteger(decimalValue), width)};

            foreach (var constant in constants)
            {
                Assert.AreEqual(expectedString, constant.ToString());
                CheckType(constant, t => t.IsBv);
                Assert.AreEqual(width, constant.asBvConst.Bits);
                Assert.AreEqual(width, constant.Type.BvBits);

                // Compute decimal representation of two's complement bv
                var MaxValuePlusOne = BigInteger.Pow(2, width);
                var expectedValue = (MaxValuePlusOne + decimalValue) % MaxValuePlusOne;

                Assert.AreEqual(expectedValue, constant.asBvConst.Value.ToBigInteger);
            }
        }
    }
}

