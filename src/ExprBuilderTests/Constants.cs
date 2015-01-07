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
            var builder = new SimpleExprBuilder();
            var constant = builder.True;
            Assert.AreEqual("true", constant.ToString());

            Assert.IsNotNull(constant.Type);
            Assert.AreEqual(constant.ShallowType, constant.Type);
            Assert.IsTrue(constant.Type.IsBool);

            var constant2 = builder.ConstantBool(true);
            Assert.AreEqual("true", constant2.ToString());

            Assert.IsNotNull(constant2.Type);
            Assert.AreEqual(constant2.ShallowType, constant.Type);
            Assert.IsTrue(constant2.Type.IsBool);
        }

        [Test()]
        public void False()
        {
            var builder = new SimpleExprBuilder();
            var constant = builder.False;
            Assert.AreEqual("false", constant.ToString());

            Assert.IsNotNull(constant.Type);
            Assert.AreEqual(constant.ShallowType, constant.Type);
            Assert.IsTrue(constant.Type.IsBool);

            var constant2 = builder.ConstantBool(false);
            Assert.AreEqual("false", constant2.ToString());

            Assert.IsNotNull(constant2.Type);
            Assert.AreEqual(constant2.ShallowType, constant.Type);
            Assert.IsTrue(constant2.Type.IsBool);
        }
    }
}

