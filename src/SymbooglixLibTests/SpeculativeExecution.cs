using NUnit.Framework;
using System;
using Symbooglix;
using Symbooglix.Solver;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class SpeculativeExecution : SymbooglixTest
    {
        [Test()]
        public void NonSpeculative()
        {
            p = loadProgram("programs/TwoPaths.bpl");

            // By using a real solver both paths will not be speculative because the
            // solver is guaranteed to not return UNKNOWN because the paths are so simple
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());

            int pathCount = 0;
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                Assert.IsTrue(data.Name == "truebb" || data.Name == "falsebb");
                ++pathCount;
            };

            e.StateTerminated += delegate(object executor, Executor.ExecutionStateEventArgs data)
            {
                Assert.IsFalse(data.State.Speculative);
            };

            var counter = new TerminationCounter();
            counter.Connect(e);

            e.Run(getMain(p));

            Assert.AreEqual(2, pathCount);

            Assert.AreEqual(2, counter.Sucesses);
            Assert.AreEqual(0, counter.DisallowedSpeculativePaths);
        }

        private void SpeculativeTest(bool useLookAheadGoto)
        {
            p = loadProgram("programs/TwoPaths.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = getExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));
            e.UseGotoLookAhead = useLookAheadGoto;

            int breakPointsHit = 0;
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                Assert.IsTrue(data.Name == "truebb" || data.Name == "falsebb");
                ++breakPointsHit;
            };

            int statesTerminated = 0;
            e.StateTerminated += delegate(object executor, Executor.ExecutionStateEventArgs data)
            {
                Assert.IsTrue(data.State.Speculative);
                ++statesTerminated;
            };

            e.Run(getMain(p));

            Assert.AreEqual(0, breakPointsHit);
            Assert.AreEqual(2, statesTerminated);
        }

        [Test()]
        public void SpeculativeLookAheadGoto()
        {
            SpeculativeTest(true);
        }

        [Test()]
        public void SpeculativeNaiveGoto()
        {
            SpeculativeTest(false);
        }

        [Test()]
        public void SpeculativeDueToUnsatAxiom()
        {
            p = loadProgram("programs/InconsistentAxioms.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = getExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));

            int statesTerminated = 0;
            e.StateTerminated += delegate(object executor, Executor.ExecutionStateEventArgs data)
            {
                Assert.IsInstanceOfType(typeof(TerminatedAtUnsatisfiableAxiom), data.State.TerminationType);
                Assert.IsTrue(data.State.Speculative);
                ++statesTerminated;
            };

            try
            {
                e.Run(getMain(p));
            }
            catch(ExecuteTerminatedStateException)
            {
                // Ignore
            }

            Assert.AreEqual(1, statesTerminated);
        }

        [Test()]
        public void SpeculativeDueToFailingAssert()
        {
            p = loadProgram("programs/assert_nontrivial.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = getExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));

            int statesTerminated = 0;
            bool hitFailingAssert = false;
            e.StateTerminated += delegate(object executor, Executor.ExecutionStateEventArgs data)
            {
                Assert.IsTrue(data.State.Speculative);

                if (data.State.TerminationType is TerminatedAtFailingAssert)
                    hitFailingAssert = true;

                ++statesTerminated;
            };

            try
            {
                e.Run(getMain(p));
            }
            catch(ExecuteTerminatedStateException)
            {
                // Ignore
            }

            Assert.AreEqual(2, statesTerminated);
            Assert.IsTrue(hitFailingAssert);
        }
    }
}

