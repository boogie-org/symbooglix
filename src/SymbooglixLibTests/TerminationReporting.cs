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
    public class TerminationReporting : SymbooglixTest
    {
        public TerminationCounter Counter;

        public void InitAndRun(string program)
        {
            Counter = new TerminationCounter();
            p = LoadProgramFrom(program);
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            Counter.Connect(e);

            try
            {
                e.Run(GetMain(p));
            }
            catch (InitialStateTerminated)
            {
                // Ignore this
            }
        }

        [Test()]
        public void FailingAssert()
        {
            InitAndRun("programs/assert_false.bpl");
            Assert.AreEqual(1,Counter.FailingAsserts);
        }

        [Test()]
        public void TerminateWithoutError()
        {
            InitAndRun("programs/assert_true.bpl");
            Assert.AreEqual(0, Counter.FailingAsserts);
            Assert.AreEqual(Counter.Sucesses, 1);
        }

        [Test()]
        public void UnsatAssume()
        {
            InitAndRun("programs/assume_false.bpl");
            Assert.AreEqual(1,Counter.UnsatisfiableAssumes);
        }

        [Test()]
        public void UnsatEntryRequires()
        {
            InitAndRun("programs/UnsatisfiableEntryRequires.bpl");
            Assert.AreEqual(1, Counter.UnsatisfiableRequiresOnEntry);
            Assert.AreEqual(0, Counter.Sucesses);
            Assert.AreEqual(1, Counter.NumberOfFailures);
        }

        [Test()]
        public void FailingRequires()
        {
            InitAndRun("programs/FailingRequires.bpl");
            Assert.AreEqual(1, Counter.FailingRequires);
            Assert.AreEqual(0, Counter.Sucesses);
            Assert.AreEqual(1, Counter.NumberOfFailures);
        }

        [Test()]
        public void FailingEnsures()
        {
            InitAndRun("programs/FailingEnsures.bpl");
            Assert.AreEqual(1, Counter.FailingEnsures);
            Assert.AreEqual(0, Counter.Sucesses);
            Assert.AreEqual(1, Counter.NumberOfFailures);
        }

        [Test()]
        public void UnsatEnsures()
        {
            InitAndRun("programs/UnsatisfiableEnsures.bpl");
            Assert.AreEqual(1, Counter.UnsatisfiableEnsures);
            Assert.AreEqual(0, Counter.Sucesses);
            Assert.AreEqual(1, Counter.NumberOfFailures);
        }

        [Test()]
        public void UnsatAxiom()
        {
            InitAndRun("programs/InconsistentAxioms.bpl");
            Assert.AreEqual(1, Counter.UnsatisfiableAxioms);
            Assert.AreEqual(0, Counter.Sucesses);
            Assert.AreEqual(1, Counter.NumberOfFailures);
        }

        [Test()]
        public void DisallowedSpeculativeExecutionPath()
        {
            p = LoadProgramFrom("programs/TwoPaths.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = GetExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));

            this.Counter = new TerminationCounter(TerminationCounter.CountType.ONLY_NON_SPECULATIVE);
            var speculativeCounter = new TerminationCounter(TerminationCounter.CountType.ONLY_SPECULATIVE);
            Counter.Connect(e);
            speculativeCounter.Connect(e);

            e.Run(GetMain(p));

            Assert.AreEqual(0, Counter.DisallowedSpeculativePaths);
            Assert.AreEqual(0, Counter.Sucesses);
            Assert.AreEqual(0, Counter.NumberOfFailures);
            Assert.AreEqual(0, Counter.NumberOfTerminatedStates);

            Assert.AreEqual(2, speculativeCounter.DisallowedSpeculativePaths);
            Assert.AreEqual(0, speculativeCounter.Sucesses);
            Assert.AreEqual(0, speculativeCounter.NumberOfFailures);
            Assert.AreEqual(2, speculativeCounter.NumberOfTerminatedStates);
        }

        [Test()]
        public void UnexplorableGotos()
        {
            p = LoadProgramFrom("programs/GotoUnsatTargets.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(GetMain(p));

            Assert.AreEqual(0, counter.Sucesses);
            Assert.AreEqual(1, counter.UnexplorableGotos);
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

            var counter = new TerminationCounter();
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            counter.Connect(e);

            bool initialStateTerminated = false;
            try
            {
                e.Run(GetMain(p));
            }
            catch (InitialStateTerminated)
            {
                initialStateTerminated = true;
            }

            Assert.AreEqual(0, counter.Sucesses);
            Assert.AreEqual(1, counter.UnsatsifiableUniqueConstants);
            Assert.AreEqual(1, counter.NumberOfFailures);
            Assert.AreEqual(1, counter.NumberOfTerminatedStates);
            Assert.IsTrue(initialStateTerminated);
        }
    }
}

