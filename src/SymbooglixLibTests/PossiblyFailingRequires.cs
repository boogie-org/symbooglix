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
    public class PossiblyFailingRequires : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = LoadProgramFrom("programs/PossiblyFailingRequires.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            bool inFoo = false;
            bool pastAssertion = false;
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name == "in_foo")
                {
                    Assert.IsFalse(inFoo);
                    inFoo = true;
                }
                else if (data.Name == "past_assertion")
                {
                    Assert.IsFalse(pastAssertion);
                    pastAssertion = true;
                }
                else
                    Assert.Fail("Unexpected break point");
            };

            var terminationCounter = new TerminationCounter();
            terminationCounter.Connect(e);

            e.Run(GetMain(p));
            Assert.IsTrue(inFoo);
            Assert.IsTrue(pastAssertion);

            Assert.AreEqual(1, terminationCounter.FailingRequires);
            Assert.AreEqual(1, terminationCounter.Sucesses);
            Assert.AreEqual(2, terminationCounter.NumberOfTerminatedStates);
        }
    }
}

