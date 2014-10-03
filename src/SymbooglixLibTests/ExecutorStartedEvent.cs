using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class ExecutorStartedEvent : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = loadProgram("programs/GotoSinglePath.bpl");
            e = getExecutor(p);

            bool started = false;
            e.ExecutorStarted += delegate(object sender, Executor.ExecutorStartedArgs executorStartedArgs)
            {
                started = true;
            };

            e.Run(getMain(p));

            Assert.IsTrue(started);
        }
    }
}

