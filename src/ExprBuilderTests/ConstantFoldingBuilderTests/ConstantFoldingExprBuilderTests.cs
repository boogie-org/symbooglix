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
using System.Collections;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ExprBuilderTests
{
    public class ConstantFoldingExprBuilderTests : SimpleExprBuilderTestBase
    {
        protected Tuple<SimpleExprBuilder, ConstantFoldingExprBuilder> GetSimpleAndConstantFoldingBuilder()
        {
            var simpleBuilder = GetSimpleBuilder();
            var constantFoldingBuilder = new ConstantFoldingExprBuilder(simpleBuilder);
            return new Tuple<SimpleExprBuilder, ConstantFoldingExprBuilder>(simpleBuilder, constantFoldingBuilder);
        }

        protected ConstantFoldingExprBuilder GetConstantFoldingBuilder()
        {
            return new ConstantFoldingExprBuilder(GetSimpleBuilder());
        }
    }
}

