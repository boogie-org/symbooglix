using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class ExecutorNonTerminatedStateRemovedEvent : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = loadProgram("programs/InfiniteLoop.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());

            var tc = new TerminationCounter();
            int counter = 0;
            e.NonTerminatedStateRemoved += delegate(object sender, Executor.ExecutionStateEventArgs eventArgs)
            {
                Assert.IsFalse(eventArgs.State.Finished());
                Assert.IsNull(eventArgs.State.TerminationType);

                // FIXME: Id should **NOT* be a static counter because it is shared across all Executors which is bad
                //Assert.AreEqual(0, eventArgs.State.Id);

                ++counter;
            };

            tc.Connect(e);

            // Run with timeout
            e.Run(getMain(p),2);
            Assert.AreEqual(1, counter);
            Assert.AreEqual(0, tc.NumberOfTerminatedStates);
        }
    }
}

