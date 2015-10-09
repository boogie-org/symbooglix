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
using Symbooglix.Transform;
using Microsoft.Boogie;
using SymbooglixLibTests;
using System.Linq;

namespace TransformTests
{
    [TestFixture()]
    public class NestedFunctionsToInline
    {
        [Test()]
        public void TestCase()
        {
            Program program = SymbooglixTest.LoadProgramFrom("Transforms/programs/NestedFunctionsToInline.bpl");

            var PM = new PassManager();
            PM.Add(new FunctionInliningPass());
            PM.Run(program);

            // Check the Expression on the AssertCmd was inlined as expected
            var assert = SymbooglixTest.GetMain(program).Blocks[0].Cmds[0] as AssertCmd;
            Assert.AreEqual("v + 1 + v + 1 + 1 == 12", assert.Expr.ToString());
        }
    }
}

