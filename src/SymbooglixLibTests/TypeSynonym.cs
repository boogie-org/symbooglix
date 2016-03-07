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
    public class TypeSynonym : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = LoadProgramFrom("programs/TypeSynonym.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            var counter = new TerminationCounter();
            counter.Connect(e);

            e.Run(GetMain(p));

            Assert.AreEqual(0, counter.NumberOfFailures);
            Assert.AreEqual(1, counter.Sucesses);
        }

        [Test()]
        public void NestedTypeSynonym()
        {
            p = LoadProgramFrom(@"
                type ref = int;
                type blob = ref;
                type XXX = blob;

                procedure main()
                {
                  var myvar:XXX;
                  assume(myvar == 0);
                  assert(myvar == 0);
                }
            ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var tc = new TerminationCounter();
            tc.Connect(e);

            e.Run(GetMain(p));

            Assert.AreEqual(1, tc.NumberOfTerminatedStates);
            Assert.AreEqual(0, tc.NumberOfFailures);
            Assert.AreEqual(0, e.Statistics.ForkCount);
        }
    }
}

