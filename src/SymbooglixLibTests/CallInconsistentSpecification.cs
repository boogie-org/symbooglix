using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class CallInconsistentSpecification : SymbooglixTest
    {
        [Test()]
        public void InvalidRequires()
        {
            p = loadProgram("programs/CallInconsistentSpecification.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());

            var TC = new TerminationCounter();
            TC.Connect(e);
            e.Run(getMain(p));

            Assert.AreEqual(0, TC.Sucesses);
            Assert.AreEqual(2, TC.FailingRequires);
            Assert.AreEqual(2, TC.NumberOfTerminatedStates);
        }
    }
}

