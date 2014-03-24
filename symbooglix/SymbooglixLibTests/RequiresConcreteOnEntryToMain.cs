using System;
using NUnit.Framework;
using Microsoft.Boogie;
using symbooglix;

namespace SymbooglixLibTests
{
    public class RequiresConcreteOnEntryToMain
    {
        public Executor e;
        public Program p;

     
        private class Handler : IBreakPointHandler
        {
            public bool reachable = false;
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                if (name == "now_concrete")
                {
                    Variable v = e.currentState.getInScopeVariableAndExprByName("a").Key;
                    Assert.IsFalse(e.isSymbolic(v));
                }

                if (name == "reachable")
                    reachable = true;

                return Executor.HandlerAction.CONTINUE;
            }
        }

        [Test()]
        public void concreteLocal()
        {
            p = TestHelper.loadProgram("programs/RequiresConcreteLocal.bpl");
            e = TestHelper.getExecutor(p);
            var handler = new Handler();
            e.registerBreakPointHandler(handler);
            e.run(TestHelper.getMain(p));

            Assert.IsTrue(handler.reachable); // Check the assertion passed by checkng we explore beyond it
        }

        [Test()]
        public void concreteGlobal()
        {
            p = TestHelper.loadProgram("programs/RequiresConcreteGlobal.bpl");
            e = TestHelper.getExecutor(p);
            var handler = new Handler();
            e.registerBreakPointHandler(handler);
            e.run(TestHelper.getMain(p));

            Assert.IsTrue(handler.reachable); // Check the assertion passed by checkng we explore beyond it
        }


    }
}

