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
    public class GotoAssumeLookAhead : SymbooglixTest
    {
        [Test()]
        public void AllTargetsUnSat()
        {
            p = LoadProgramFrom("programs/GotoUnsatTargets.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(GetMain(p));

            Assert.AreEqual(0, counter.Sucesses);
            Assert.AreEqual(1, counter.NumberOfTerminatedStates);
            Assert.AreEqual(1, counter.UnexplorableGotos);
        }

        [Test()]
        public void AllTargetsWithSatisfiableAssumes()
        {
            p = LoadProgramFrom("programs/GotoAllSatTargets.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(GetMain(p));

            Assert.AreEqual(3, counter.Sucesses);
            Assert.AreEqual(0, counter.NumberOfFailures);
        }

        [Test()]
        public void AllTargetsWithoutAssumes()
        {
            p = LoadProgramFrom("programs/GotoAllTargetsWithoutAssumes.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(GetMain(p));

            Assert.AreEqual(3, counter.Sucesses);
            Assert.AreEqual(0, counter.NumberOfFailures);
        }

        [Test()]
        public void TargetsMixedAssumes()
        {
            p = LoadProgramFrom("programs/GotoTargetsMixedAssumes.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var counter = new TerminationCounter();
            counter.Connect(e);

            int breakpointCounter = 0;
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs breakPointEventArgs)
            {
                ++breakpointCounter;
            };

            e.Run(GetMain(p));

            Assert.AreEqual(3, counter.Sucesses);
            Assert.AreEqual(0, counter.NumberOfFailures);

            Assert.AreEqual(3, breakpointCounter);
        }
    }
}

