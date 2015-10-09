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
    public class ExecutorExplicitBranchDepth : SymbooglixTest
    {
        private void SingleGoto(bool useGotoLookAhead)
        {
            p = LoadProgramFrom("programs/GotoMultiplePaths.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = useGotoLookAhead;

            int successCounter = 0;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs executionStateEventArgs)
            {
                if (executionStateEventArgs.State.TerminationType is TerminatedWithoutError)
                {
                    Assert.AreEqual(1, executionStateEventArgs.State.ExplicitBranchDepth);
                    ++successCounter;
                }
            };

            e.Run(GetMain(p));
            Assert.AreEqual(3, successCounter);
        }

        [Test()]
        public void SingleGotoLookAheadGoto()
        {
            SingleGoto(true);
        }

        [Test()]
        public void SingleGotoNaiveGoto()
        {
            SingleGoto(false);
        }


        private void ConcreteLoop(bool useGotoLookAhead)
        {
            p = LoadProgramFrom("programs/ConcreteLoop.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = useGotoLookAhead;

            int successCounter = 0;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs executionStateEventArgs)
            {
                if (executionStateEventArgs.State.TerminationType is TerminatedWithoutError)
                {
                    // The depth is the loop bound +1 because the loop head is visited once more so it can leave the loop
                    Assert.AreEqual(4, executionStateEventArgs.State.ExplicitBranchDepth);
                    ++successCounter;
                }
            };

            e.Run(GetMain(p));
            Assert.AreEqual(1, successCounter);
        }

        [Test()]
        public void ConcreteLoopLookAheadGoto()
        {
            ConcreteLoop(true);
        }

        [Test()]
        public void ConcreteLoopNaiveGoto()
        {
            ConcreteLoop(false);
        }

        private void SingleGotoOneTarget(bool useGotoLookAhead)
        {
            p = LoadProgramFrom("programs/GotoSinglePath.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = useGotoLookAhead;

            int successCounter = 0;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs executionStateEventArgs)
            {
                // The goto only has a single target to the ExplicitBranchDepth should not be increased
                Assert.AreEqual(0, executionStateEventArgs.State.ExplicitBranchDepth);
                ++successCounter;
            };

            e.Run(GetMain(p));
            Assert.AreEqual(1, successCounter);
        }

        [Test()]
        public void SingleGotoOneTargetLookAheadGoto()
        {
            SingleGotoOneTarget(true);
        }

        [Test()]
        public void SingleGotoOneTargetNaiveGoto()
        {
            SingleGotoOneTarget(false);
        }
    }
}

