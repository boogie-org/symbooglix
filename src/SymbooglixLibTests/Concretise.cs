using Microsoft.Boogie;
using NUnit.Framework;
using Symbooglix;
using System;
using System.Diagnostics;
using System.Linq;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Concretise : SymbooglixTest
    {
        public int hits = 0;

        [SetUp()]
        public void Init()
        {
            p = LoadProgramFrom("programs/Concretise.bpl");
            e = GetExecutor(p);
        }

        public void checkConcrete(Object executor, Executor.BreakPointEventArgs eventArgs)
        {
            if (eventArgs.Name == "entry")
            {
                ++hits;

                // Check globals are symbolic
                foreach (Variable V in e.CurrentState.Mem.Globals.Keys)
                    Assert.IsTrue(e.IsSymbolic(V));

                // Check globals are symbolic
                foreach (Variable V in e.CurrentState.GetCurrentStackFrame().Locals.Keys)
                    Assert.IsTrue(e.IsSymbolic(V));

                return;
            }

            Assert.AreEqual(1, hits);
            Assert.AreEqual("now_concrete", eventArgs.Name);
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
        }
       

        [Test()]
        public void Run()
        {
            e.BreakPointReached += checkConcrete;
            e.Run(GetMain(p));
            Assert.AreEqual(2, hits);
        }


    }
}

