using Microsoft.Boogie;
using NUnit.Framework;
using symbooglix;
using System;
using System.Linq;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class GlobalConstant
    {
        Program p;
        Executor e;

        [SetUp()]
        public void Init()
        {
            p = TestHelper.loadProgram("programs/GlobalSymbolicConstant.bpl");
            e = TestHelper.getExecutor(p);
        }

        private class GlobalConstantHandler : IBreakPointHandler
        {
            private Program prog;
            private bool shouldBeSymbolic;
            public GlobalConstantHandler(Program p, bool shouldBeSymbolic) {prog = p; this.shouldBeSymbolic = shouldBeSymbolic;}

            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                Assert.IsTrue(name == "entry");
                var constant = prog.TopLevelDeclarations.OfType<Constant>().Where( c => c.Name == "a").First();
                Assert.IsTrue(constant is Constant);

                Assert.IsTrue( e.currentState.isInScopeVariable(constant));

                if (shouldBeSymbolic)
                    Assert.IsTrue(e.isSymbolic(constant));
                else
                    Assert.IsFalse(e.isSymbolic(constant));

                return Executor.HandlerAction.CONTINUE;
            }
        }
        [Test()]
        public void GlobalSymbolicConstant()
        {
            p = TestHelper.loadProgram("programs/GlobalSymbolicConstant.bpl");
            e = TestHelper.getExecutor(p);
            e.registerBreakPointHandler(new GlobalConstantHandler(p, true));
            e.run(TestHelper.getMain(p));
        }

        [Test()]
        public void GlobalConstantWithAxiom()
        {
            p = TestHelper.loadProgram("programs/GlobalConstantWithAxiom.bpl");
            e = TestHelper.getExecutor(p);
            e.registerBreakPointHandler(new GlobalConstantHandler(p, false));
            e.run(TestHelper.getMain(p));
        }
    }
}

