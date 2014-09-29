using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class GotoAssumeLookAhead : SymbooglixTest
    {
        [Test()]
        public void AllTargetsUnSat()
        {
            p = loadProgram("programs/GotoUnsatTargets.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(getMain(p));

            // FIXME: Check for failed state.
        }

        [Test()]
        public void AllTargetsWithSatisfiableAssumes()
        {
            p = loadProgram("programs/GotoAllSatTargets.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(getMain(p));

            Assert.AreEqual(3, counter.Sucesses);
            Assert.AreEqual(0, counter.NumberOfFailures);
        }

        [Test()]
        public void AllTargetsWithoutAssumes()
        {
            p = loadProgram("programs/GotoAllTargetsWithoutAssumes.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(getMain(p));

            Assert.AreEqual(3, counter.Sucesses);
            Assert.AreEqual(0, counter.NumberOfFailures);
        }

        [Test()]
        public void TargetsMixedAssumes()
        {
            p = loadProgram("programs/GotoTargetsMixedAssumes.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var counter = new TerminationCounter();
            counter.Connect(e);

            int breakpointCounter = 0;
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs breakPointEventArgs)
            {
                ++breakpointCounter;
            };

            e.Run(getMain(p));

            Assert.AreEqual(3, counter.Sucesses);
            Assert.AreEqual(0, counter.NumberOfFailures);

            Assert.AreEqual(3, breakpointCounter);
        }
    }
}

