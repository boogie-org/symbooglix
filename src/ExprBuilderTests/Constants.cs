using NUnit.Framework;
using System;
using Symbooglix;
using Microsoft.Basetypes;
using System.Numerics;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class Constants
    {
        private void CheckType(Microsoft.Boogie.LiteralExpr e, Predicate<Microsoft.Boogie.Type> p)
        {
            Assert.IsNotNull(e.ShallowType);
            Assert.IsTrue(p(e.ShallowType));
            Assert.IsNotNull(e.Type);
            Assert.AreEqual(e.ShallowType, e.Type);
        }

        [Test()]
        public void True()
        {
            var builder = new SimpleExprBuilder();
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
            var builder = new SimpleExprBuilder();
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
            var builder = new SimpleExprBuilder();
            var constant = builder.ConstantInt(5);
            Assert.AreEqual("5", constant.ToString());
            Assert.AreEqual(5, constant.asBigNum.ToInt);
            CheckType(constant, t => t.IsInt);
        }

        [Test()]
        public void NegativeInteger()
        {
            var builder = new SimpleExprBuilder();
            var constant = builder.ConstantInt(-5);
            Assert.AreEqual("-5", constant.ToString());
            Assert.AreEqual(-5, constant.asBigNum.ToInt);
            CheckType(constant, t => t.IsInt);
        }

        [Test()]
        public void PositiveReal()
        {
            var builder = new SimpleExprBuilder();
            var constant = builder.ConstantReal("5.0");
            Assert.AreEqual("5e0", constant.ToString());
            CheckType(constant, t => t.IsReal);
        }

        [Test()]
        public void NegativeReal()
        {
            var builder = new SimpleExprBuilder();
            var constant = builder.ConstantReal("-5.0");
            Assert.AreEqual("-5e0", constant.ToString());
            CheckType(constant, t => t.IsReal);
        }

        [TestCase(5, 4, "5bv4")]
        [TestCase(11, 32, "11bv32")]
        [TestCase(0, 4, "0bv4")]
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
            var builder = new SimpleExprBuilder();
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
            var builder = new SimpleExprBuilder();
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

