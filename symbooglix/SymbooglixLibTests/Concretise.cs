using Microsoft.Boogie;
using NUnit.Framework;
using symbooglix;
using System;
using System.Diagnostics;
using System.Linq;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Concretise : IBreakPointHandler
    {
        public Executor e;
        public Program p;
        public int hits = 0;

        [SetUp()]
        public void Init()
        {
            p = TestHelper.loadProgram("programs/Concretise.bpl");
            e = TestHelper.getExecutor(p);
        }

        public Executor.HandlerAction handleBreakPoint(string name, Executor e)
        {
            if (name == "entry")
            {
                ++hits;

                // Check globals are symbolic
                foreach (Variable V in e.currentState.mem.globals.Keys)
                    Assert.IsTrue(e.isSymbolic(V));

                // Check globals are symbolic
                foreach (Variable V in e.currentState.getCurrentStackFrame().locals.Keys)
                    Assert.IsTrue(e.isSymbolic(V));

                return Executor.HandlerAction.CONTINUE;
            }

            Assert.AreEqual(hits, 1);
            Assert.AreEqual(name, "now_concrete");
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
            e.run(TestHelper.getMain(p));
            Assert.AreEqual(hits, 2);
        }


    }
}

