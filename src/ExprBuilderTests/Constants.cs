using NUnit.Framework;
using System;
using Symbooglix;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class Constants
    {
        [Test()]
        public void True()
        {
            var builder = new ExprBuilder();
            var constant = builder.True;
            Assert.AreEqual("true", constant.ToString());

            var constant2 = builder.ConstantBool(true);
            Assert.AreEqual("true", constant2.ToString());
        }

        [Test()]
        public void False()
        {
            var builder = new ExprBuilder();
            var constant = builder.False;
            Assert.AreEqual("false", constant.ToString());

            var constant2 = builder.ConstantBool(false);
            Assert.AreEqual("false", constant2.ToString());
        }
    }
}

