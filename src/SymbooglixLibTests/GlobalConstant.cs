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
        [Test()]
        public void GlobalSymbolicConstant()
        {
            p = LoadProgramFrom("programs/GlobalSymbolicConstant.bpl");
            e = GetExecutor(p);
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                Assert.IsTrue(data.Name == "entry");
                var constant = p.TopLevelDeclarations.OfType<Constant>().Where( c => c.Name == "a").First();
                Assert.IsTrue(constant is Constant);
                Assert.IsTrue(e.CurrentState.IsInScopeVariable(constant));
                Assert.IsTrue(e.IsSymbolic(constant));

                // No constraint for a constant
            };
            e.Run(GetMain(p));
        }

        [Test()]
        public void GlobalConstantWithAxiom()
        {
            p = LoadProgramFrom("programs/GlobalConstantWithAxiom.bpl");
            e = GetExecutor(p);
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                Assert.IsTrue(data.Name == "entry");
                var constant = p.TopLevelDeclarations.OfType<Constant>().Where( c => c.Name == "a").First();
                Assert.IsTrue(constant is Constant);
                Assert.IsTrue(e.CurrentState.IsInScopeVariable(constant));
                Assert.IsFalse(e.IsSymbolic(constant)); // There is an equality constraint that forces this to be concrete

                // Find the symbolic associated with Constant
                var relevantSymbolic = e.CurrentState.Symbolics.Where( s => s.Origin.IsVariable && s.Origin.AsVariable == constant).First();

                // Check for the expect equality constraint.
                bool found = false;
                foreach (Expr constraint in e.CurrentState.Constraints.ConstraintExprs)
                {
                    LiteralExpr literal = null;
                    if (FindLiteralAssignment.find(constraint, relevantSymbolic, out literal))
                    {
                        found = true;
                        Assert.IsTrue(literal.isBvConst);
                        Assert.AreEqual(literal.asBvConst.Value.ToInt, 7);
                    }
                }
                Assert.IsTrue(found, "Did not find expected equality constraint");
            };
            e.Run(GetMain(p));
        }

        [Test()]
        public void GlobalConstantWithWeakerAxiom()
        {
            p = LoadProgramFrom("programs/GlobalConstantWithWeakerAxiom.bpl");
            e = GetExecutor(p);
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                Assert.IsTrue(data.Name == "entry");
                var constant = p.TopLevelDeclarations.OfType<Constant>().Where( c => c.Name == "a").First();
                Assert.IsTrue(constant is Constant);
                Assert.IsTrue(e.CurrentState.IsInScopeVariable(constant));
                Assert.IsTrue(e.IsSymbolic(constant));

                // Find the symbolic associated with Constant
                var relevantSymbolic = e.CurrentState.Symbolics.Where( s => s.Origin.IsVariable && s.Origin.AsVariable == constant).First();

                // Check for the expected constraint
                bool found = false;
                foreach (Expr constraint in e.CurrentState.Constraints.ConstraintExprs)
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
                Assert.IsTrue(found, "Did not find expected Neq constraint");

            };
            e.Run(GetMain(p));
        }
    }
}

