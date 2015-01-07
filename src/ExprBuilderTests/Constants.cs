using NUnit.Framework;
using System;
using Symbooglix;
using Microsoft.Basetypes;

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
    }
}

