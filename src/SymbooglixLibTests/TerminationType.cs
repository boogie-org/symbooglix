using NUnit.Framework;
using System;
using Symbooglix;
using Symbooglix.Solver;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class TerminationType : SymbooglixTest
    {
        public void InitAndRun<T>(string program)
        {
            int counter = 0;
            p = loadProgram(program);
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());

            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs state)
            {
                Assert.IsInstanceOfType(typeof(T), state.State.TerminationType);
                ++counter;
            };

            try
            {
                e.Run(getMain(p));
            }
            catch (ExecuteTerminatedStateException)
            {
                // Ignore for now
            }

            Assert.AreEqual(1, counter);
        }

        [Test()]
        public void FailingAssert()
        {
            InitAndRun<TerminatedAtFailingAssert>("programs/assert_false.bpl");
        }

        [Test()]
        public void TerminateWithoutError()
        {
            InitAndRun<TerminatedWithoutError>("programs/assert_true.bpl");
        }


        [Test()]
        public void UnsatAssume()
        {
            InitAndRun<TerminatedAtUnsatisfiableAssume>("programs/assume_false.bpl");
        }


        [Test()]
        public void UnsatEntryRequires()
        {
            InitAndRun<TerminatedAtUnsatisfiableEntryRequires>("programs/UnsatisfiableEntryRequires.bpl");
        }


        [Test()]
        public void FailingRequires()
        {
            InitAndRun<TerminatedAtFailingRequires>("programs/FailingRequires.bpl");

        }

        [Test()]
        public void FailingEnsures()
        {
            InitAndRun<TerminatedAtFailingEnsures>("programs/FailingEnsures.bpl");
        }

        [Test()]
        public void UnsatEnsures()
        {
            InitAndRun<TerminatedAtUnsatisfiableEnsures>("programs/UnsatisfiableEnsures.bpl");
        }

        [Test()]
        public void UnsatAxiom()
        {
            InitAndRun<TerminatedAtUnsatisfiableAxiom>("programs/InconsistentAxioms.bpl");
        }

        [Test()]
        public void DisallowedSpeculativeExecutionPath()
        {
            p = loadProgram("programs/TwoPaths.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = getExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));

            int counter = 0;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs stateArgs)
            {
                Assert.IsInstanceOfType(typeof(TerminatedWithDisallowedSpeculativePath), stateArgs.State.TerminationType);
                ++counter;
            };

            e.Run(getMain(p));
            Assert.AreEqual(2, counter);
        }
    }
}

