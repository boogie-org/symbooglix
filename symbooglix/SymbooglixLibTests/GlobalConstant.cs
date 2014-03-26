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

        private class GlobalSymbolicConstantHandler : IBreakPointHandler
        {
            private Program prog;
            public GlobalSymbolicConstantHandler(Program p) {prog = p;}

            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                Assert.IsTrue(name == "entry");
                var constant = prog.TopLevelDeclarations.OfType<Constant>().Where( c => c.Name == "a").First();
                Assert.IsTrue(constant is Constant);

                Assert.IsTrue( e.currentState.isInScopeVariable(constant));

                Assert.IsTrue(e.isSymbolic(constant));

                return Executor.HandlerAction.CONTINUE;
            }
        }
        [Test()]
        public void GlobalSymbolicConstant()
        {
            e.registerBreakPointHandler(new GlobalSymbolicConstantHandler(p));
            e.run(TestHelper.getMain(p));
        }
    }
}

