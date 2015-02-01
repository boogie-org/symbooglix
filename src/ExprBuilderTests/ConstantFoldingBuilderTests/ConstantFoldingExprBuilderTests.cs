using NUnit.Framework;
using System;
using System.Collections;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class ConstantFoldingExprBuilderTests : SimpleExprBuilderTestBase
    {
        protected Tuple<IExprBuilder, IExprBuilder> GetSimpleAndConstantFoldingBuilder()
        {
            var simpleBuilder = GetBuilder();
            var constantFoldingBuilder = new ConstantFoldingExprBuilder(simpleBuilder);
            return new Tuple<IExprBuilder, IExprBuilder>(simpleBuilder, constantFoldingBuilder);
        }
    }
}

