using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class RequiresWithConstantEqualityConstraint : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = loadProgram("programs/RequiresWithConstantEqualityConstraint.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(getMain(p));

            Assert.AreEqual(1, counter.Sucesses);
            Assert.AreEqual(0, counter.NumberOfFailures);
        }
    }
}

