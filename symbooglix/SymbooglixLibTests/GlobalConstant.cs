using Microsoft.Boogie;
using NUnit.Framework;
using symbooglix;
using System;
using System.Linq;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class GlobalConstant : SymbooglixTest
    {
        private class GlobalConstantHandler : IBreakPointHandler
        {
            private Program prog;
            private bool shouldBeSymbolic;
            private bool shouldHaveConstraint;
            public GlobalConstantHandler(Program p, bool shouldBeSymbolic, bool shouldHaveConstraint)
            {
                prog = p;
                this.shouldBeSymbolic = shouldBeSymbolic;
                this.shouldHaveConstraint = shouldHaveConstraint;
            }

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

                if (shouldHaveConstraint)
                {
                    // FIXME: This is totally broken. We need a proper way of finding
                    // the symbolic associated with a variable.
                    Expr symbolic_for_a= e.currentState.getInScopeVariableExpr(constant);
                    var FSV = new FindSymbolicsVisitor(e.currentState);
                    FSV.Visit(symbolic_for_a);
                    Assert.IsTrue(FSV.symbolics.Count() > 0);
                    string expected = ( symbolic_for_a as IdentifierExpr ).Name + " != 7bv8";
                    Assert.IsTrue(e.currentState.cm.constraints[0].ToString() == expected);
                }

                return Executor.HandlerAction.CONTINUE;
            }
        }
        [Test()]
        public void GlobalSymbolicConstant()
        {
            p = loadProgram("programs/GlobalSymbolicConstant.bpl");
            e = getExecutor(p);
            e.registerBreakPointHandler(new GlobalConstantHandler(p, true, false));
            e.run(getMain(p));
        }

        [Test()]
        public void GlobalConstantWithAxiom()
        {
            p = loadProgram("programs/GlobalConstantWithAxiom.bpl");
            e = getExecutor(p);
            e.registerBreakPointHandler(new GlobalConstantHandler(p, false, true));
            e.run(getMain(p));
        }

        [Test()]
        public void GlobalConstantWithWeakerAxiom()
        {
            p = loadProgram("programs/GlobalConstantWithWeakerAxiom.bpl");
            e = getExecutor(p);
            e.registerBreakPointHandler(new GlobalConstantHandler(p, true, true));
            e.run(getMain(p));
        }
    }
}

