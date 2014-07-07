using NUnit.Framework;
using System;
using Microsoft.Basetypes;
using Microsoft.Boogie;
using System.Numerics;

namespace BoogieTests
{
    [TestFixture()]
    public class BigDecParseFromString
    {
        [Test()]
        public void TestCase()
        {
            // This tests for a Bug in Boogie that existed at the
            // time of writing this test where BigDec would not parse
            // strings with negative numbers correctly
            //
            // If this bug is present this test will fail when checking
            // the mantissa
            var v = BigDec.FromString("-1.5");
            Assert.AreEqual(-1, v.Exponent);
            Assert.AreEqual(new BigInteger(-15.0), v.Mantissa);
        }
    }
}

