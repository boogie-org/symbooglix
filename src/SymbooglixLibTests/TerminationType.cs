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
using Symbooglix.Solver;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class TerminationType : SymbooglixTest
    {
        public T InitAndRun<T>(string program) where T:class,ITerminationType
        {
            int counter = 0;
            p = LoadProgramFrom(program);
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver(), /*useConstantFolding=*/ false);

            T terminationType = null;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs eventArgs)
            {
                Assert.IsInstanceOf<T>(eventArgs.State.TerminationType);
                terminationType = eventArgs.State.TerminationType as T;
                ++counter;

                Assert.IsFalse(eventArgs.State.Speculative);
                Assert.AreEqual(1, terminationType.ExitLocation.InstrStatistics.Terminations);
            };

            try
            {
                e.Run(GetMain(p));
            }
            catch (InitialStateTerminated)
            {
                // Ignore for now
            }

            Assert.AreEqual(1, counter);
            return terminationType;
        }

        public T InitAndRunWithSuccessAndFailure<T>(string program) where T:class
        {
            int counter = 0;
            p = LoadProgramFrom(program);
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            T terminationType = null;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs eventArgs)
            {
                if (eventArgs.State.TerminationType is T)
                    terminationType = eventArgs.State.TerminationType as T;

                ++counter;
                Assert.IsFalse(eventArgs.State.Speculative);
            };

            try
            {
                e.Run(GetMain(p));
            }
            catch (InitialStateTerminated)
            {
                // Ignore for now
            }

            Assert.AreEqual(2, counter);
            Assert.IsInstanceOf<T>(terminationType);
            return terminationType;
        }

        [Test()]
        public void FailingAssertConstant()
        {
            var terminationType = InitAndRun<TerminatedAtFailingAssert>("programs/assert_false.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("false", terminationType.ConditionForUnsat.ToString());
            Assert.AreEqual("!false", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void FailingAssertNotConstant()
        {
            var terminationType = InitAndRun<TerminatedAtFailingAssert>("programs/FailingAssertNonTrivial.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("~sb_x_0 < 0", terminationType.ConditionForUnsat.ToString());
            Assert.AreEqual("!(~sb_x_0 < 0)", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void FailingAndSuceedingAssert()
        {
            var terminationType = InitAndRunWithSuccessAndFailure<TerminatedAtFailingAssert>("programs/FailingAndSucceedingAssert.bpl");

            Assert.IsNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("!(~sb_x_0 <= 0)", terminationType.ConditionForSat.ToString());
            Assert.AreEqual(1, terminationType.ExitLocation.AsCmd.GetInstructionStatistics().Terminations);
        }

        [Test()]
        public void TerminateWithoutError()
        {
            var terminationType = InitAndRun<TerminatedWithoutError>("programs/assert_true.bpl");
            Assert.AreEqual(1, terminationType.State.Mem.Stack.Count);
        }


        [Test()]
        public void UnsatAssumeConstant()
        {
            var terminationType = InitAndRun<TerminatedAtUnsatisfiableAssume>("programs/assume_false.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.AreEqual("false", terminationType.ConditionForUnsat.ToString());
        }

        [Test()]
        public void UnsatAssume()
        {
            var terminationType = InitAndRun<TerminatedAtUnsatisfiableAssume>("programs/UnsatisfiableAssume.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.AreEqual("~sb_x_0 * ~sb_x_0 < ~sb_x_0", terminationType.ConditionForUnsat.ToString());
        }


        [Test()]
        public void UnsatEntryRequires()
        {
            var terminationType = InitAndRun<TerminatedAtUnsatisfiableEntryRequires>("programs/UnsatisfiableEntryRequires.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.AreEqual("~sb_x_0 < 0", terminationType.ConditionForUnsat.ToString());
        }


        [Test()]
        public void FailingRequires()
        {
            var terminationType = InitAndRun<TerminatedAtFailingRequires>("programs/FailingRequires.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("~sb_x_0 > 0", terminationType.ConditionForUnsat.ToString());
            Assert.AreEqual("!(~sb_x_0 > 0)", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void FailingAndSucceedingRequires()
        {
            var terminationType = InitAndRunWithSuccessAndFailure<TerminatedAtFailingRequires>("programs/FailingAndSucceedingRequires.bpl");

            Assert.IsNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("!(~sb_x_0 > 0)", terminationType.ConditionForSat.ToString());
            Assert.AreEqual(1, terminationType.ExitLocation.AsRequires.GetInstructionStatistics().Terminations);
        }

        [Test()]
        public void FailingEnsures()
        {
            var terminationType = InitAndRun<TerminatedAtFailingEnsures>("programs/FailingEnsures.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("~sb_x_0 > 0", terminationType.ConditionForUnsat.ToString());
            Assert.AreEqual("!(~sb_x_0 > 0)", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void FailingAndSucceedingEnsures()
        {
            var terminationType = InitAndRunWithSuccessAndFailure<TerminatedAtFailingEnsures>("programs/FailingAndSucceedingEnsures.bpl");

            Assert.IsNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("!(~sb_x_0 > 0)", terminationType.ConditionForSat.ToString());
            Assert.AreEqual(1, terminationType.ExitLocation.AsEnsures.GetInstructionStatistics().Terminations);
        }

        [Test()]
        public void UnsatEnsures()
        {
            var terminationType = InitAndRun<TerminatedAtUnsatisfiableEnsures>("programs/UnsatisfiableEnsures.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.AreEqual("~sb_r_0 > 20", terminationType.ConditionForUnsat.ToString());

            Assert.IsNotNull(terminationType.ConditionForSat);
            Assert.AreEqual("!(~sb_r_0 > 20)", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void UnsatAxiom()
        {
            var terminationType = InitAndRun<TerminatedAtUnsatisfiableAxiom>("programs/InconsistentAxioms.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.AreEqual("~sb_g_0 < 0", terminationType.ConditionForUnsat.ToString());
            Assert.IsNotNull(terminationType.ConditionForSat);
            Assert.AreEqual("!(~sb_g_0 < 0)", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void DisallowedSpeculativeExecutionPath()
        {
            p = LoadProgramFrom("programs/TwoPaths.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = GetExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));

            int counter = 0;
            ITerminationType terminationType = null;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs stateArgs)
            {
                terminationType = stateArgs.State.TerminationType;
                Assert.IsInstanceOf<TerminatedWithDisallowedSpeculativePath>(terminationType);
                ++counter;
                Assert.IsTrue(stateArgs.State.Speculative);
            };

            e.Run(GetMain(p));
            Assert.AreEqual(2, counter);

            // Check Terminations statistic
            Assert.AreEqual(1, terminationType.ExitLocation.InstrStatistics.Terminations);
        }

        [Test()]
        public void UnexplorableGotos()
        {
            p = LoadProgramFrom("programs/GotoUnsatTargets.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            int counter = 0;
            ITerminationType terminationType = null;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs executionStateEventArgs)
            {
                Assert.IsInstanceOf<TerminatedAtGotoWithUnsatisfiableTargets>(executionStateEventArgs.State.TerminationType);
                terminationType = executionStateEventArgs.State.TerminationType;
                ++counter;
                Assert.IsFalse(executionStateEventArgs.State.Speculative);
            };
            e.Run(GetMain(p));

            Assert.AreEqual(1, counter);
            Assert.AreEqual(1, terminationType.ExitLocation.AsTransferCmd.GetInstructionStatistics().Terminations);
        }

        [Test()]
        public void DisallowedDepth()
        {
            var scheduler = new LimitExplicitDepthScheduler(new DFSStateScheduler(), 1);
            p = LoadProgramFrom("programs/SimpleLoop.bpl");
            e = GetExecutor(p, scheduler, GetSolver());

            int hit = 0;
            var main = GetMain(p);

            var loopBody = main.Blocks[2];
            Assert.AreEqual("loopBody", loopBody.Label);
            var loopDone = main.Blocks[3];
            Assert.AreEqual("loopDone", loopDone.Label);

            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs eventArgs)
            {
                switch (hit)
                {
                    case 0:
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.State.TerminationType);
                        Assert.AreEqual(1, eventArgs.State.ExplicitBranchDepth);
                        break;
                    case 1:
                        // We expect the first label (loopDone) to be killed first as the CurrentState always follows the left most available GotoCmd target
                        Assert.IsInstanceOf<TerminatedWithDisallowedExplicitBranchDepth>(eventArgs.State.TerminationType);
                        Assert.AreEqual(2, eventArgs.State.ExplicitBranchDepth);
                        Assert.AreEqual(loopDone, eventArgs.State.GetCurrentBlock());
                        break;
                    case 2:
                        Assert.IsInstanceOf<TerminatedWithDisallowedExplicitBranchDepth>(eventArgs.State.TerminationType);
                        Assert.AreEqual(2, eventArgs.State.ExplicitBranchDepth);
                        Assert.AreEqual(loopBody, eventArgs.State.GetCurrentBlock());
                        break;
                    default:
                        Assert.Fail("To many terminations");
                        break;
                }
                ++hit;
            };


            e.Run(main);
            Assert.AreEqual(3, hit);
        }

        [Test()]
        public void UnsatUniqueAttribute()
        {
            p = LoadProgramFrom(@"
            const unique a:int;
            const unique b:int;
            axiom a == b;

            procedure main()
            {
                var x:int;
                x := a;
            }

            ", "test.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            int counter = 0;
            TerminatedWithUnsatisfiableUniqueAttribute terminationType = null;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs executionStateEventArgs)
            {
                Assert.IsInstanceOf<TerminatedWithUnsatisfiableUniqueAttribute>(executionStateEventArgs.State.TerminationType);
                terminationType = executionStateEventArgs.State.TerminationType as TerminatedWithUnsatisfiableUniqueAttribute;
                ++counter;
                Assert.IsFalse(executionStateEventArgs.State.Speculative);
            };
            try
            {
                e.Run(GetMain(p));
            }
            catch (InitialStateTerminated)
            {

            }

            Assert.AreEqual(1, counter);
            Assert.AreEqual("distinct(~sb_a_0, ~sb_b_0)", terminationType.ConditionForUnsat.ToString());
            Assert.AreEqual("!distinct(~sb_a_0, ~sb_b_0)", terminationType.ConditionForSat.ToString());
        }
    }
}

