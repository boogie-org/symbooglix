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
                foreach (Variable V in e.currentState.mem.Globals.Keys)
                    Assert.IsTrue(e.isSymbolic(V));

                // Check globals are symbolic
                foreach (Variable V in e.currentState.getCurrentStackFrame().Locals.Keys)
                    Assert.IsTrue(e.isSymbolic(V));

                return Executor.HandlerAction.CONTINUE;
            }

            Assert.AreEqual(1, hits);
            Assert.AreEqual("now_concrete", name);
            ++hits;

            // Check "a" is now concrete
            Variable varA = e.currentState.getInScopeVariableAndExprByName("a").Key;
            Assert.IsFalse(e.isSymbolic(varA));

            // Check "x" is now concrete
            Variable varX = e.currentState.getInScopeVariableAndExprByName("x").Key;
            Assert.IsFalse(e.isSymbolic(varX));

            // Check "y" is still symbolic
            Variable varY = e.currentState.getInScopeVariableAndExprByName("y").Key;
            Assert.IsTrue(e.isSymbolic(varY));

            return Executor.HandlerAction.STOP;
        }
       

        [Test()]
        public void Run()
        {
            e.registerBreakPointHandler(this);
            e.run(getMain(p));
            Assert.AreEqual(2, hits);
        }


    }
}

