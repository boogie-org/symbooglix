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
    public class ExecutorTimeout : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = LoadProgramFrom("programs/InfiniteLoop.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var tc = new TerminationCounter();

            tc.Connect(e);

            bool timeoutHit = false;
            e.ExecutorTimeoutReached += delegate(object sender, Executor.ExecutorTimeoutReachedArgs eventArgs)
            {
                timeoutHit = true;
            };

            e.ExecutorTerminated += delegate(object sender, Executor.ExecutorTerminatedArgs eventArgs)
            {
                Assert.AreEqual(Executor.ExecutorTerminationType.TIMEOUT, eventArgs.TerminationType);
            };

            // Run with timeout
            e.Run(GetMain(p),3);
            Assert.AreEqual(0, tc.NumberOfTerminatedStates);
            Assert.IsTrue(timeoutHit);
        }
    }
}

