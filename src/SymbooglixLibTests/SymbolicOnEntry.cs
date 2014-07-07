using Microsoft.Boogie;
using NUnit.Framework;
using Symbooglix;
using System;
using System.Diagnostics;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class SymbolicOnEntry : SymbooglixTest
    {
        [SetUp()]
        public void Init()
        {
            p = loadProgram("programs/SymbolicOnEntry.bpl");
            e = getExecutor(p);
        }

        private class GlobalsAreSymbolicHandler : IBreakPointHandler
        {
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                Assert.IsTrue(name == "entry");
                e.CurrentState.DumpStackTrace();
                // Check that all globals are symbolic
                foreach (GlobalVariable GV in e.CurrentState.Mem.Globals.Keys)
                {
                    Assert.IsTrue(e.IsSymbolic(GV));
                }

                return Executor.HandlerAction.STOP;
            }
        }

        [Test()]
        public void GlobalsAreSymbolic()
        {
            e.RegisterBreakPointHandler(new GlobalsAreSymbolicHandler());
            e.Run(getMain(p));
        }

        private class LocalsAreSymbolicHandler : IBreakPointHandler
        {
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                Assert.IsTrue(name == "entry");
                e.CurrentState.DumpStackTrace();
                // Check that all locals are symbolic
                foreach (Variable LV in e.CurrentState.GetCurrentStackFrame().Locals.Keys)
                {
                    Assert.IsTrue(e.IsSymbolic(LV));
                }

                return Executor.HandlerAction.STOP;
            }
        }

        [Test()]
        public void LocalsAreSymbolic()
        {
            e.RegisterBreakPointHandler(new LocalsAreSymbolicHandler());
            e.Run(getMain(p));
        }


    }
}

