using Microsoft.Boogie;
using NUnit.Framework;
using Symbooglix;
using System;
using System.Diagnostics;
using System.Linq;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Concretise : SymbooglixTest, IBreakPointHandler
    {
        public int hits = 0;

        [SetUp()]
        public void Init()
        {
            p = loadProgram("programs/Concretise.bpl");
            e = getExecutor(p);
        }

        public Executor.HandlerAction handleBreakPoint(string name, Executor e)
        {
            if (name == "entry")
            {
                ++hits;

                // Check globals are symbolic
                foreach (Variable V in e.CurrentState.Mem.Globals.Keys)
                    Assert.IsTrue(e.IsSymbolic(V));

                // Check globals are symbolic
                foreach (Variable V in e.CurrentState.GetCurrentStackFrame().Locals.Keys)
                    Assert.IsTrue(e.IsSymbolic(V));

                return Executor.HandlerAction.CONTINUE;
            }

            Assert.AreEqual(1, hits);
            Assert.AreEqual("now_concrete", name);
            ++hits;

            // Check "a" is now concrete
            Variable varA = e.CurrentState.GetInScopeVariableAndExprByName("a").Key;
            Assert.IsFalse(e.IsSymbolic(varA));

            // Check "x" is now concrete
            Variable varX = e.CurrentState.GetInScopeVariableAndExprByName("x").Key;
            Assert.IsFalse(e.IsSymbolic(varX));

            // Check "y" is still symbolic
            Variable varY = e.CurrentState.GetInScopeVariableAndExprByName("y").Key;
            Assert.IsTrue(e.IsSymbolic(varY));

            return Executor.HandlerAction.STOP;
        }
       

        [Test()]
        public void Run()
        {
            e.RegisterBreakPointHandler(this);
            e.Run(getMain(p));
            Assert.AreEqual(2, hits);
        }


    }
}

