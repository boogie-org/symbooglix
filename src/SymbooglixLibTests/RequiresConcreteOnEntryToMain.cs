using System;
using NUnit.Framework;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using Symbooglix;

namespace SymbooglixLibTests
{
    public class RequiresConcreteOnEntryToMain : SymbooglixTest
    {
        private class Handler : IBreakPointHandler
        {
            public bool reachable = false;
            public bool isBvConst = true;
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                if (name == "now_concrete")
                {
                    Variable v = e.currentState.GetInScopeVariableAndExprByName("a").Key;
                    Assert.IsFalse(e.isSymbolic(v));
                }

                if (name == "reachable")
                {
                    reachable = true;

                    // Check that the equality constraint has been stored
                    bool found = false;
                    foreach (Expr constraint in e.currentState.Constraints.constraints)
                    {
                        //Variable v = e.currentState.getInScopeVariableAndExprByName("a").Key;

                        foreach (var s in e.currentState.Symbolics)
                        {
                            Assert.IsTrue(s.expr is IdentifierExpr);
                            var id = s.expr as IdentifierExpr;
                            LiteralExpr literal = null;
                            found = FindLiteralAssignment.find(constraint, id.Decl, out literal);

                            if (found)
                            {
                                if (isBvConst && literal.isBvConst && literal.asBvConst.Value == BigNum.FromInt(2)) // check its value
                                    break;
                                else if (!isBvConst && literal.isBool && literal.IsTrue)
                                    break;
                                else
                                    found = false;
                            }
                        }

                        if (found)
                            break;

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

        [Test()]
        public void concreteLocalBool()
        {
            p = loadProgram("programs/RequiresConcreteLocalBool.bpl");
            e = getExecutor(p);
            var handler = new Handler();
            handler.isBvConst = false;
            e.registerBreakPointHandler(handler);
            e.run(getMain(p));

            Assert.IsTrue(handler.reachable, "Did not reach last assertion"); // Check the assertion passed by checkng we explore beyond it
        }


    }
}

