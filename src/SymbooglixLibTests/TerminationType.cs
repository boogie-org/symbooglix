using NUnit.Framework;
using System;
using Symbooglix;
using Symbooglix.Solver;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class TerminationType : SymbooglixTest
    {
        public T InitAndRun<T>(string program) where T:class
        {
            int counter = 0;
            p = loadProgram(program);
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());

            T terminationType = null;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs state)
            {
                Assert.IsInstanceOfType(typeof(T), state.State.TerminationType);
                terminationType = state.State.TerminationType as T;
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
            return terminationType;
        }

        public T InitAndRunWithSuccessAndFailure<T>(string program) where T:class
        {
            int counter = 0;
            p = loadProgram(program);
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());

            T terminationType = null;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs state)
            {
                if (state.State.TerminationType is T)
                    terminationType = state.State.TerminationType as T;

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

            Assert.AreEqual(2, counter);
            Assert.IsInstanceOfType(typeof(T), terminationType);
            return terminationType;
        }

        [Test()]
        public void FailingAssertConstant()
        {
            var terminationType = InitAndRun<TerminatedAtFailingAssert>("programs/assert_false.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("false", terminationType.ConditionForUnsat.ToString());
            Assert.AreEqual("true", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void FailingAssertNotConstant()
        {
            var terminationType = InitAndRun<TerminatedAtFailingAssert>("programs/FailingAssertNonTrivial.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("symbolic_0 < 0", terminationType.ConditionForUnsat.ToString());
            Assert.AreEqual("0 <= symbolic_0", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void FailingAndSuceedingAssert()
        {
            var terminationType = InitAndRunWithSuccessAndFailure<TerminatedAtFailingAssert>("programs/FailingAndSucceedingAssert.bpl");

            Assert.IsNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("0 < symbolic_0", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void TerminateWithoutError()
        {
            InitAndRun<TerminatedWithoutError>("programs/assert_true.bpl");
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
            Assert.AreEqual("symbolic_0 * symbolic_0 < symbolic_0", terminationType.ConditionForUnsat.ToString());
        }


        [Test()]
        public void UnsatEntryRequires()
        {
            var terminationType = InitAndRun<TerminatedAtUnsatisfiableEntryRequires>("programs/UnsatisfiableEntryRequires.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.AreEqual("symbolic_0 < 0", terminationType.ConditionForUnsat.ToString());
        }


        [Test()]
        public void FailingRequires()
        {
            var terminationType = InitAndRun<TerminatedAtFailingRequires>("programs/FailingRequires.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("symbolic_0 > 0", terminationType.ConditionForUnsat.ToString());
            Assert.AreEqual("0 >= symbolic_0", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void FailingAndSucceedingRequires()
        {
            var terminationType = InitAndRunWithSuccessAndFailure<TerminatedAtFailingRequires>("programs/FailingAndSucceedingRequires.bpl");

            Assert.IsNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("0 >= symbolic_0", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void FailingEnsures()
        {
            var terminationType = InitAndRun<TerminatedAtFailingEnsures>("programs/FailingEnsures.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("symbolic_1 > 0", terminationType.ConditionForUnsat.ToString());
            Assert.AreEqual("0 >= symbolic_1", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void FailingAndSucceedingEnsures()
        {
            var terminationType = InitAndRunWithSuccessAndFailure<TerminatedAtFailingEnsures>("programs/FailingAndSucceedingEnsures.bpl");

            Assert.IsNull(terminationType.ConditionForUnsat);
            Assert.IsNotNull(terminationType.ConditionForSat);

            Assert.AreEqual("0 >= symbolic_1", terminationType.ConditionForSat.ToString());
        }

        [Test()]
        public void UnsatEnsures()
        {
            var terminationType = InitAndRun<TerminatedAtUnsatisfiableEnsures>("programs/UnsatisfiableEnsures.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.AreEqual("symbolic_1 > 20", terminationType.ConditionForUnsat.ToString());
        }

        [Test()]
        public void UnsatAxiom()
        {
            var terminationType = InitAndRun<TerminatedAtUnsatisfiableAxiom>("programs/InconsistentAxioms.bpl");

            Assert.IsNotNull(terminationType.ConditionForUnsat);
            Assert.AreEqual("symbolic_0 < 0", terminationType.ConditionForUnsat.ToString());
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

        [Test()]
        public void UnexplorableGotos()
        {
            p = loadProgram("programs/GotoUnsatTargets.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            int counter = 0;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs executionStateEventArgs)
            {
                Assert.IsInstanceOfType(typeof(TerminatedAtGotoWithUnsatisfiableTargets), executionStateEventArgs.State.TerminationType);
                ++counter;
            };
            e.Run(getMain(p));

            Assert.AreEqual(1, counter);
        }
    }
}

