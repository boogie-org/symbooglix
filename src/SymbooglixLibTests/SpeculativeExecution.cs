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
            p = LoadProgramFrom("programs/TwoPaths.bpl");

            // By using a real solver both paths will not be speculative because the
            // solver is guaranteed to not return UNKNOWN because the paths are so simple
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

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

            e.Run(GetMain(p));

            Assert.AreEqual(2, pathCount);

            Assert.AreEqual(2, counter.Sucesses);
            Assert.AreEqual(0, counter.DisallowedSpeculativePaths);
        }

        private void SpeculativeTest(bool useLookAheadGoto)
        {
            p = LoadProgramFrom("programs/TwoPaths.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = GetExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));
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

            e.Run(GetMain(p));

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
            p = LoadProgramFrom("programs/InconsistentAxioms.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = GetExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));

            int statesTerminated = 0;
            e.StateTerminated += delegate(object executor, Executor.ExecutionStateEventArgs data)
            {
                Assert.IsInstanceOf<TerminatedWithDisallowedSpeculativePath>(data.State.TerminationType);
                Assert.IsTrue(data.State.Speculative);
                Assert.IsTrue(data.State.TerminationType.ExitLocation.IsAxiom);
                ++statesTerminated;
            };

            try
            {
                e.Run(GetMain(p));
            }
            catch(InitialStateTerminated)
            {
                // Ignore
            }

            Assert.AreEqual(1, statesTerminated);
        }

        [Test()]
        public void SpeculativeDueToFailingAssert()
        {
            p = LoadProgramFrom("programs/assert_nontrivial.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = GetExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));

            int statesTerminated = 0;
            bool hitFailingAssert = false;
            e.StateTerminated += delegate(object executor, Executor.ExecutionStateEventArgs data)
            {
                Assert.IsTrue(data.State.Speculative);

                if (data.State.TerminationType is TerminatedWithDisallowedSpeculativePath)
                {
                    if (data.State.TerminationType.ExitLocation.IsCmd && data.State.TerminationType.ExitLocation.AsCmd is Microsoft.Boogie.AssertCmd)
                    hitFailingAssert = true;
                }

                ++statesTerminated;
            };

            try
            {
                e.Run(GetMain(p));
            }
            catch(InitialStateTerminated)
            {
                // Ignore
            }

            Assert.AreEqual(2, statesTerminated);
            Assert.IsTrue(hitFailingAssert);
        }

        [Test()]
        public void SpeculativeAtAssume()
        {
            p = LoadProgramFrom("programs/assume_nontrivial.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = GetExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));

            int statesTerminated = 0;
            e.StateTerminated += delegate(object executor, Executor.ExecutionStateEventArgs data)
            {
                Assert.IsTrue(data.State.Speculative);
                Assert.IsInstanceOf<TerminatedWithDisallowedSpeculativePath>(data.State.TerminationType);

                Assert.IsTrue(data.State.GetCurrentStackFrame().CurrentInstruction.Current is Microsoft.Boogie.AssumeCmd);

                ++statesTerminated;
            };


            e.Run(GetMain(p));
            Assert.AreEqual(1, statesTerminated);
        }
    }
}

