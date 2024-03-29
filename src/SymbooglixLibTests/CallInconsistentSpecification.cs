//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2017 Daniel Liew
//
// This file is licensed under the MIT license.
// See LICENSE.txt for details.
//------------------------------------------------------------------------------
using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class CallInconsistentSpecification : SymbooglixTest
    {
        [Test()]
        public void InvalidRequires()
        {
            p = LoadProgramFrom("programs/CallInconsistentSpecification.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var TC = new TerminationCounter();
            TC.Connect(e);
            e.Run(GetMain(p));

            Assert.AreEqual(0, TC.Sucesses);
            Assert.AreEqual(2, TC.FailingRequires);
            Assert.AreEqual(2, TC.NumberOfTerminatedStates);
        }
    }
}

