//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
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
            e.UseGlobalDDE = false; // Need to disable otherwise "a" will be removed
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
                //var relevantSymbolic = e.CurrentState.Symbolics.Where( s => s.Origin.IsVariable && s.Origin.AsVariable == constant).First();

                // Check for the expect equality constraint.
                bool found = false;
                foreach (Expr constraint in e.CurrentState.Constraints.ConstraintExprs)
                {
                    LiteralExpr literal = null;
                    Variable symbolic = null;
                    if (FindLiteralAssignment.findAnyVariable(constraint, out symbolic, out literal))
                    {
                        Assert.IsInstanceOf<SymbolicVariable>(symbolic);
                        var asSym = symbolic as SymbolicVariable;
                        if( asSym.Origin.IsVariable && asSym.Origin.AsVariable == constant)
                        {
                            found = true;
                            Assert.IsTrue(literal.isBvConst);
                            Assert.AreEqual(literal.asBvConst.Value.ToInt, 7);
                        }
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

                // Check for the expected constraint
                bool found = false;
                foreach (Expr constraint in e.CurrentState.Constraints.ConstraintExprs)
                {
                    var asNeq = ExprUtil.AsNotEq(constraint);
                    if (asNeq != null)
                    {
                        var asSymVar = ExprUtil.AsSymbolicVariable(asNeq.Args[0]);
                        Assert.IsNotNull(asSymVar);
                        Assert.IsTrue(asSymVar.Origin.IsVariable && asSymVar.Origin.AsVariable == constant);
                        Assert.IsTrue(asNeq.Args[1] is LiteralExpr && ( asNeq.Args[1] as LiteralExpr ).asBvConst.Value.ToInt == 7);
                        found = true;
                    }
                }
                Assert.IsTrue(found, "Did not find expected Neq constraint");

            };
            e.Run(GetMain(p));
        }
    }
}

