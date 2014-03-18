using Microsoft.Boogie;
using NUnit.Framework;
using symbooglix;
using System;
using System.Diagnostics;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class SymbolicOnEntry
    {
        public Executor e;
        public Program p;

        [SetUp()]
        public void Init()
        {
            p = TestHelper.loadProgram("programs/SingleProcedure.bpl");
            e = TestHelper.getExecutor(p);
        }

        private class GlobalsAreSymbolicHandler : IBreakPointHandler
        {
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                Assert.IsTrue(name == "entry");
                e.currentState.dumpStackTrace();
                // Check that all globals are symbolic
                foreach (GlobalVariable GV in e.currentState.mem.globals.Keys)
                {
                    Assert.IsTrue(e.isSymbolic(GV));
                }

                return Executor.HandlerAction.STOP;
            }
        }

        [Test()]
        public void GlobalsAreSymbolic()
        {
            e.registerBreakPointHandler(new GlobalsAreSymbolicHandler());
            e.run(TestHelper.getMain(p));
        }

        private class LocalsAreSymbolicHandler : IBreakPointHandler
        {
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                Assert.IsTrue(name == "entry");
                e.currentState.dumpStackTrace();
                // Check that all locals are symbolic
                foreach (Variable LV in e.currentState.getCurrentStackFrame().locals.Keys)
                {
                    Assert.IsTrue(e.isSymbolic(LV));
                }

                return Executor.HandlerAction.STOP;
            }
        }

        [Test()]
        public void LocalsAreSymbolic()
        {
            e.registerBreakPointHandler(new LocalsAreSymbolicHandler());
            e.run(TestHelper.getMain(p));
        }


    }
}

