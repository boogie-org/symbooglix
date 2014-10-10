using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class ExecutorContextChangeEvent : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = loadProgram("programs/GotoMultiplePaths.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());

            int count = 0;
            e.ContextChanged += delegate(object sender, Executor.ContextChangeEventArgs contextChangeEventArgs)
            {
                ++count;
            };

            e.Run(getMain(p));

            Assert.AreEqual(2, count);
        }
    }
}

