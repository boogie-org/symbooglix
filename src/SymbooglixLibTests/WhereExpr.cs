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
    public class WhereExpr : SymbooglixTest
    {
        [Test(),ExpectedException(typeof(NotImplementedException))]
        public void LocalVariable()
        {
            p = LoadProgramFrom("programs/WhereExpr.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(GetMain(p));

            Assert.AreEqual(0, counter.NumberOfFailures);
            Assert.AreEqual(1, counter.Sucesses);
        }

        [Test(),ExpectedException(typeof(NotImplementedException))]
        public void GlobalVariable()
        {
            p = LoadProgramFrom("programs/GlobalWhereExpr.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(GetMain(p));

            Assert.AreEqual(0, counter.NumberOfFailures);
            Assert.AreEqual(1, counter.Sucesses);
        }
    }
}

