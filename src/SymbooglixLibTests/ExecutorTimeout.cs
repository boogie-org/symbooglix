using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class ExecutorTimeout : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = loadProgram("programs/InfiniteLoop.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());

            var tc = new TerminationCounter();

            tc.Connect(e);

            // Run with timeout
            e.Run(getMain(p),3);
            Assert.AreEqual(0, tc.NumberOfTerminatedStates);

        }
    }
}

