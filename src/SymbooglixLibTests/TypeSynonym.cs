using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class TypeSynonym : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = LoadProgramFrom("programs/TypeSynonym.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            var counter = new TerminationCounter();
            counter.Connect(e);

            e.Run(GetMain(p));

            Assert.AreEqual(0, counter.NumberOfFailures);
            Assert.AreEqual(1, counter.Sucesses);
        }
    }
}

