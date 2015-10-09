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
using Symbooglix;
using System;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class MapExtensionality : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p= LoadProgramFrom("programs/MapExtensionality.bpl");
            var executor = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            executor.StateTerminated += delegate(object e, Executor.ExecutionStateEventArgs data) 
            {
                var terminationType = data.State.TerminationType;
                if (terminationType is TerminatedAtFailingAssert)
                    Assert.Fail("Boogie assertion failed");

                if (terminationType is TerminatedAtUnsatisfiableAssume)
                    Assert.Fail("Boogie assume failed");
            };
            executor.Run(GetMain(p));

        }
    }
}

