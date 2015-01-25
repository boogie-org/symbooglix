using System;
using NUnit.Framework;
using Microsoft.Boogie;
using Symbooglix;

namespace ExprBuilderTests
{
    public class Old
    {
        public Old()
        {
            // This is a hack
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();
        }

        private IExprBuilder GetBuilder()
        {
            return new SimpleExprBuilder();
        }

        [Test()]
        public void SimpleOld()
        {
            var builder = GetBuilder();
            var constant = builder.ConstantBV(0, 8);
            var result = builder.Old(constant);
            Assert.AreEqual("old(0bv8)", result.ToString());
            Assert.AreEqual(BasicType.GetBvType(8), result.ShallowType);
            Assert.IsNotNull(result.Type);
            Assert.AreEqual(BasicType.GetBvType(8), result.Type);
        }
    }
}

