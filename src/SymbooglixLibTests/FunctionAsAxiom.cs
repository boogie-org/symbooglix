using NUnit.Framework;
using Symbooglix;
using System;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class FunctionAsAxiom : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = loadProgram("programs/functionAsAxiom.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
            var counter = new TerminationCounter();
            e.RegisterTerminationHandler(counter);
            e.Run(getMain(p));

            Assert.AreEqual(1, counter.Sucesses);
            Assert.AreEqual(0, counter.NumberOfFailures);
        }
    }
}

