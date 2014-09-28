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

        [Test()]
        public void Speculative()
        {
            p = loadProgram("programs/TwoPaths.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = getExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));

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
    }
}

