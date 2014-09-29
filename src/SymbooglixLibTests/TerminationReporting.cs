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
            p = loadProgram(program);
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
            Counter.Connect(e);

            try
            {
                e.Run(getMain(p));
            }
            catch (ExecuteTerminatedStateException)
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
            p = loadProgram("programs/TwoPaths.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = getExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));

            this.Counter = new TerminationCounter();
            Counter.Connect(e);

            e.Run(getMain(p));

            Assert.AreEqual(2, Counter.DisallowedSpeculativePaths);
            Assert.AreEqual(0, Counter.Sucesses);
            Assert.AreEqual(0, Counter.NumberOfFailures);
        }

        [Test()]
        public void UnexplorableGotos()
        {
            p = loadProgram("programs/GotoUnsatTargets.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(getMain(p));

            Assert.AreEqual(0, counter.Sucesses);
            Assert.AreEqual(1, counter.UnexplorableGotos);
        }
    }
}

