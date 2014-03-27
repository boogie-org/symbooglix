using NUnit.Framework;
using System;
using symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Goto : SymbooglixTest
    {

        private class SingleTargetHandler : IBreakPointHandler
        {
            public int hits=0;
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                if (name == "entry")
                {
                    // FIXME: This is fragile, find a way to name the entry block
                    Assert.AreEqual("anon0", e.currentState.getCurrentStackFrame().currentBlock.Label);
                    ++hits;
                }

                if (name == "reached")
                {
                    Assert.AreEqual("NEXT", e.currentState.getCurrentStackFrame().currentBlock.Label);
                    ++hits;
                }

                return Executor.HandlerAction.CONTINUE;
            }
        }
        [Test()]
        public void SingleTarget()
        {
            p = loadProgram("programs/GotoSinglePath.bpl");
            e = getExecutor(p);
            var handler = new SingleTargetHandler();
            e.registerBreakPointHandler(handler);
            e.run(getMain(p));
            Assert.AreEqual(2, handler.hits);

        }

        private class MultipleTargetHandler : IBreakPointHandler
        {
            public int hits=0;
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                if (name == "entry")
                {
                    Assert.AreEqual("anon0", e.currentState.getCurrentStackFrame().currentBlock.Label);
                    ++hits;
                }
                else if (name == "path0")
                {
                    Assert.AreEqual("P0", e.currentState.getCurrentStackFrame().currentBlock.Label);
                    ++hits;
                }
                else if (name == "path1")
                {
                    Assert.AreEqual("P1", e.currentState.getCurrentStackFrame().currentBlock.Label);
                    ++hits;
                }
                else
                {
                    Assert.Fail("Unexpected break point");
                }

                return Executor.HandlerAction.CONTINUE;
            }
        }
        [Test()]
        public void MultipleTargets()
        {
            p = loadProgram("programs/GotoMultiplePaths.bpl");
            e = getExecutor(p);
            var handler = new MultipleTargetHandler();
            e.registerBreakPointHandler(handler);
            e.run(getMain(p));
            Assert.AreEqual(3, handler.hits);
        }
    }
}

