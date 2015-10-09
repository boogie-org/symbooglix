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
using Microsoft.Boogie;
using System.Collections.Generic;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class InvalidEntryPoint : SymbooglixTest
    {
        [Test(),ExpectedException(typeof(Symbooglix.InvalidEntryPoint))]
        public void TestCase()
        {
            // It doesn't matter which program we load
            p = LoadProgramFrom("programs/assert_true.bpl");
            e = GetExecutor(p);

            var impl = new Implementation(Token.NoToken, "dummy", null, null, null, null, new List<Block>());
            e.Run(impl);
        }
    }
}

