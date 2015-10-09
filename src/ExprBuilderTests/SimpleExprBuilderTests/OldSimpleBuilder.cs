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
using Microsoft.Boogie;
using Symbooglix;

namespace ExprBuilderTests
{
    public class OldSimpleBuilder : SimpleExprBuilderTestBase
    {
        [Test()]
        public void SimpleOld()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantBV(0, 8);
            var result = builder.Old(constant);
            Assert.AreEqual("old(0bv8)", result.ToString());
            CheckIsBvType(result, 8);
        }
    }
}

