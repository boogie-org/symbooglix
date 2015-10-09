//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using NUnit.Framework;
using Symbooglix;
using Solver = Symbooglix.Solver;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class TerminateInitialState : SymbooglixTest
    {
        [Test()]
        public void simple()
        {
            p = LoadProgramFrom(@"
                const g:int;
                axiom g > 0;
                procedure main()
                {
                    return;
                }


                ", "test.bpl");

            // Always return UNKNOWN so trying to prove the axiom fails so the initial state fails to be prepared
            var solver = new Solver.SimpleSolver(new Solver.DummySolver(Solver.Result.UNKNOWN));
            e = GetExecutor(p, new DFSStateScheduler(), solver);

            // Global DDE must be disabled otherwise the axiom will be removed
            e.UseGlobalDDE = false;

            int stateTerminationCounter = 0;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs eventArgs)
            {
                ++stateTerminationCounter;

                Assert.IsInstanceOf<TerminatedAtUnsatisfiableAxiom>(eventArgs.State.TerminationType);
                var terminationType = eventArgs.State.TerminationType as TerminatedAtUnsatisfiableAxiom;
                Assert.IsTrue(terminationType.ExitLocation.IsAxiom);
            };

            bool hitException = false;
            try
            {
                e.Run(GetMain(p));
            }
            catch (InitialStateTerminated)
            {
                hitException = true;
                Assert.AreEqual(Executor.ExecutorTerminationType.INITIAL_STATE_TERMINATED, e.TerminationType);
            }
            Assert.IsTrue(hitException);
            Assert.AreEqual(1, stateTerminationCounter);
        }
    }
}

