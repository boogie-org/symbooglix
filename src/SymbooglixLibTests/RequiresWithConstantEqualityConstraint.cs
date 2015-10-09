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

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class RequiresWithConstantEqualityConstraint : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = LoadProgramFrom("programs/RequiresWithConstantEqualityConstraint.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(GetMain(p));

            Assert.AreEqual(1, counter.Sucesses);
            Assert.AreEqual(0, counter.NumberOfFailures);
        }
    }
}

