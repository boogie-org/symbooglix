using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class TerminationReporting : SymbooglixTest
    {
        public TerminationCounter Counter;

        public void InitAndRun(string program)
        {
            Counter = new TerminationCounter();
            p = loadProgram(program);
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
            Counter.Connect(e);
            e.Run(getMain(p));
        }

        [Test()]
        public void FailingAssert()
        {
            InitAndRun("programs/assert_false.bpl");
            Assert.AreEqual(Counter.FailingAsserts, 1);
        }

        [Test()]
        public void TerminateWithoutError()
        {
            InitAndRun("programs/assert_true.bpl");
            Assert.AreEqual(Counter.FailingAsserts, 0);
            Assert.AreEqual(Counter.Sucesses, 1);
        }

        [Test()]
        public void UnsatAssume()
        {
            InitAndRun("programs/assume_false.bpl");
            Assert.AreEqual(Counter.UnsatisfiableAssumes, 1);
        }

        [Test()]
        public void UnsatEntryRequires()
        {
            InitAndRun("programs/UnsatisfiableEntryRequires.bpl");
            Assert.AreEqual(1, Counter.UnsatisfiableRequiresOnEntry);
        }
    }
}

