using System;
using NUnit.Framework;
using Microsoft.Boogie;
using symbooglix;

namespace SymbooglixLibTests
{
    public class RequiresConcreteOnEntryToMain : SymbooglixTest
    {
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
                {
                    reachable = true;

                    // Check that the equality constraint has been stored
                    bool found = false;
                    foreach (Expr constraint in e.currentState.cm.constraints)
                    {
                        Variable v = e.currentState.getInScopeVariableAndExprByName("a").Key;
                        LiteralExpr literal = null;
                        found = FindLiteralAssignment.find(constraint, v, out literal);
                        if (found)
                        {
                            break;
                            // FIXME: Check literal value.
                        }
                    }
                    Assert.IsTrue(found, "Equality constraint could not be found");
                }

                return Executor.HandlerAction.CONTINUE;
            }
        }

        [Test()]
        public void concreteLocal()
        {
            p = loadProgram("programs/RequiresConcreteLocal.bpl");
            e = getExecutor(p);
            var handler = new Handler();
            e.registerBreakPointHandler(handler);
            e.run(getMain(p));

            Assert.IsTrue(handler.reachable); // Check the assertion passed by checkng we explore beyond it
        }

        [Test()]
        public void concreteGlobal()
        {
            p = loadProgram("programs/RequiresConcreteGlobal.bpl");
            e = getExecutor(p);
            var handler = new Handler();
            e.registerBreakPointHandler(handler);
            e.run(getMain(p));

            Assert.IsTrue(handler.reachable, "Did not reach last assertion"); // Check the assertion passed by checkng we explore beyond it
        }


    }
}

