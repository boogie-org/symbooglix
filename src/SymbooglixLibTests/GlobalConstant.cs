using Microsoft.Boogie;
using NUnit.Framework;
using Symbooglix;
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
            private bool equalityConstraint;
            public GlobalConstantHandler(Program p, bool shouldBeSymbolic, bool shouldHaveConstraint, bool equalityConstraint)
            {
                prog = p;
                this.shouldBeSymbolic = shouldBeSymbolic;
                this.shouldHaveConstraint = shouldHaveConstraint;
                this.equalityConstraint = equalityConstraint;
            }

            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                Assert.IsTrue(name == "entry");
                var constant = prog.TopLevelDeclarations.OfType<Constant>().Where( c => c.Name == "a").First();
                Assert.IsTrue(constant is Constant);

                Assert.IsTrue( e.CurrentState.IsInScopeVariable(constant));

                if (shouldBeSymbolic)
                    Assert.IsTrue(e.IsSymbolic(constant));
                else
                    Assert.IsFalse(e.IsSymbolic(constant));

                if (shouldHaveConstraint)
                {
                    SymbolicVariable relevantSymbolic = null;
                    foreach (SymbolicVariable SV in e.CurrentState.Symbolics)
                    {
                        // Check if it came from Variable initialisation
                        if (SV.Origin.IsVariable)
                        {
                            var V = SV.Origin.AsVariable;
                            if (V == constant)
                            {
                                // Found the symbolic that was created for the constant variable "a"
                                relevantSymbolic = SV;
                            }
                        }
                    }


                    bool found = false;
                    // FIXME: This test is getting messy, switch to delegates so the code can be an annoymous method in the test?
                    if (equalityConstraint)
                    {
                        // Check for the expect equality constraint.
                        foreach (Expr constraint in e.CurrentState.Constraints.Constraints)
                        {
                            LiteralExpr literal = null;
                            if (FindLiteralAssignment.find(constraint, relevantSymbolic, out literal))
                            {
                                found = true;
                                Assert.IsTrue(literal.isBvConst);
                                Assert.AreEqual(literal.asBvConst.Value.ToInt, 7);
                            }
                        }
                    }
                    else
                    {
                        foreach (Expr constraint in e.CurrentState.Constraints.Constraints)
                        {
                            if (constraint is NAryExpr)
                            {
                                var nary = constraint as NAryExpr;
                                if (nary.Fun is BinaryOperator)
                                {
                                    var Bop = nary.Fun as BinaryOperator;
                                    if (Bop.Op == BinaryOperator.Opcode.Neq)
                                    {
                                        found = true;
                                        Assert.IsTrue(nary.Args[0] == relevantSymbolic.Expr);
                                        Assert.IsTrue(nary.Args[1] is LiteralExpr && ( nary.Args[1] as LiteralExpr ).asBvConst.Value.ToInt == 7);
                                    }
                                }
                            }
                        }
                    }

                    Assert.IsTrue(found, "Could not find expected constraint");
                }

                return Executor.HandlerAction.CONTINUE;
            }
        }
        [Test()]
        public void GlobalSymbolicConstant()
        {
            p = loadProgram("programs/GlobalSymbolicConstant.bpl");
            e = getExecutor(p);
            e.RegisterBreakPointHandler(new GlobalConstantHandler(p, true, false, false));
            e.Run(getMain(p));
        }

        [Test()]
        public void GlobalConstantWithAxiom()
        {
            p = loadProgram("programs/GlobalConstantWithAxiom.bpl");
            e = getExecutor(p);
            e.RegisterBreakPointHandler(new GlobalConstantHandler(p, false, true, true));
            e.Run(getMain(p));
        }

        [Test()]
        public void GlobalConstantWithWeakerAxiom()
        {
            p = loadProgram("programs/GlobalConstantWithWeakerAxiom.bpl");
            e = getExecutor(p);
            e.RegisterBreakPointHandler(new GlobalConstantHandler(p, true, true, false));
            e.Run(getMain(p));
        }
    }
}

