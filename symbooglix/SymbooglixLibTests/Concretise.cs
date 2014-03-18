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

        // FIXME: This should probably be in ExecutionState
        public Variable getVariableByName(string name, ExecutionState state)
        {
            var local = ( from pair in state.getCurrentStackFrame().locals
                          where pair.Key.Name == name
                          select pair.Key );
            if (local.Count() != 0)
            {
                Assert.AreEqual(local.Count(), 1);
                return local.First();
            }

            var global = ( from pair in state.mem.globals
                           where pair.Key.Name == name
                           select pair.Key );

            Assert.AreEqual(global.Count(), 1);
            return global.First();
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
            Variable varA = getVariableByName("a", e.currentState);
            Assert.IsFalse(e.isSymbolic(varA));

            // Check "x" is now concrete
            Variable varX = getVariableByName("x", e.currentState);
            Assert.IsFalse(e.isSymbolic(varX));

            // Check "y" is still symbolic
            Variable varY = getVariableByName("y", e.currentState);
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

