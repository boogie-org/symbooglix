using Microsoft.Boogie;
using NUnit.Framework;
using System;
using Symbooglix;

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
                    Assert.AreEqual("anon0", e.CurrentState.GetCurrentStackFrame().CurrentBlock.Label);
                    ++hits;
                }
                else if (name == "reached")
                {
                    Assert.AreEqual("NEXT", e.CurrentState.GetCurrentStackFrame().CurrentBlock.Label);
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
        public void SingleTarget()
        {
            p = loadProgram("programs/GotoSinglePath.bpl");
            e = getExecutor(p);
            var handler = new SingleTargetHandler();
            e.RegisterBreakPointHandler(handler);
            e.Run(getMain(p));
            Assert.AreEqual(2, handler.hits);

        }

        private class MultipleTargetHandler : IBreakPointHandler
        {
            public int hits=0;
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                if (name == "entry")
                {
                    Assert.AreEqual("anon0", e.CurrentState.GetCurrentStackFrame().CurrentBlock.Label);
                    ++hits;
                }
                else if (name == "path0")
                {
                    Assert.AreEqual("P0", e.CurrentState.GetCurrentStackFrame().CurrentBlock.Label);
                    ++hits;

                    var a = e.CurrentState.GetInScopeVariableAndExprByName("a");
                    BvConst aBV = getBVFromLiteral(a.Value as LiteralExpr);
                    Assert.AreEqual(7, aBV.Value.ToInt);
                }
                else if (name == "path1")
                {
                    var a = e.CurrentState.GetInScopeVariableAndExprByName("a");
                    Assert.AreEqual("P1", e.CurrentState.GetCurrentStackFrame().CurrentBlock.Label);
                    BvConst aBV = getBVFromLiteral(a.Value as LiteralExpr);
                    Assert.AreEqual(8, aBV.Value.ToInt);
                    ++hits;
                }
                else if (name == "path2")
                {
                    var a = e.CurrentState.GetInScopeVariableAndExprByName("a");
                    Assert.AreEqual("P2", e.CurrentState.GetCurrentStackFrame().CurrentBlock.Label);
                    BvConst aBV = getBVFromLiteral(a.Value as LiteralExpr);
                    Assert.AreEqual(9, aBV.Value.ToInt);
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
            e.RegisterBreakPointHandler(handler);
            e.Run(getMain(p));
            Assert.AreEqual(4, handler.hits);
        }
    }
}

