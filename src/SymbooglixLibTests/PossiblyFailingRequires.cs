using NUnit.Framework;
using Symbooglix;
using System;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class PossiblyFailingRequires : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = loadProgram("programs/PossiblyFailingRequires.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());

            bool inFoo = false;
            bool pastAssertion = false;
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name == "in_foo")
                {
                    Assert.IsFalse(inFoo);
                    inFoo = true;
                }
                else if (data.Name == "past_assertion")
                {
                    Assert.IsFalse(pastAssertion);
                    pastAssertion = true;
                }
                else
                    Assert.Fail("Unexpected break point");
            };

            var terminationCounter = new TerminationCounter();
            e.RegisterTerminationHandler(terminationCounter);

            e.Run(getMain(p));
            Assert.IsTrue(inFoo);
            Assert.IsTrue(pastAssertion);

            Assert.AreEqual(1, terminationCounter.UnsatisfiableRequires);
            Assert.AreEqual(1, terminationCounter.Sucesses);
            Assert.AreEqual(2, terminationCounter.NumberOfTerminatedStates);
        }
    }
}

