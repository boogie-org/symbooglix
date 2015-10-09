//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using NUnit.Framework;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using Symbooglix;
using System.Linq;

namespace SymbooglixLibTests
{
    public class RequiresConcreteOnEntryToMain : SymbooglixTest
    {
        public void checkConcrete(Object executor, Executor.BreakPointEventArgs eventArgs)
        {
            if (eventArgs.Name == "now_concrete")
            {
                Variable v = e.CurrentState.GetInScopeVariableAndExprByName("a").Key;
                Assert.IsFalse(e.IsSymbolic(v));
            }
        }

        public void checkEqualityConstraint(object executor, Executor.BreakPointEventArgs data, Predicate<LiteralExpr> condition)
        {
            // Check that the equality constraint has been stored
            bool found = false;

            // Find the symbolic associated with variable "a".
            var theLocal = e.CurrentState.GetInScopeVariableAndExprByName("a");
            //var symbolic = e.CurrentState.Symbolics.Where( s => s.Origin.AsVariable == theLocal.Key).First();


            foreach (Expr constraint in e.CurrentState.Constraints.ConstraintExprs)
            {
                LiteralExpr literal = null;
                Variable symbolic = null;
                found = FindLiteralAssignment.findAnyVariable(constraint, out symbolic, out literal);
                if (found)
                {
                    Assert.IsInstanceOf<SymbolicVariable>(symbolic);
                    var asSym = symbolic as SymbolicVariable;
                    if (asSym.Origin.IsVariable && asSym.Origin.AsVariable == theLocal.Key)
                    {
                        Assert.IsTrue(condition(literal));
                        found = true;
                        break;
                    }
                }
            }
            Assert.IsTrue(found, "Equality constraint not found");
        }


        [Test()]
        public void concreteLocal()
        {
            bool reachable = false;
            p = LoadProgramFrom("programs/RequiresConcreteLocal.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.BreakPointReached += checkConcrete;

            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name == "now_concrete")
                    this.checkEqualityConstraint(executor, data, l => l.isBvConst && l.asBvConst.ToReadableString() == "2bv8");
                else if (data.Name == "reachable")
                    reachable = true;
                else
                    Assert.Fail("Unexpected break point \"" + data.Name + "\"");
            };
            e.Run(GetMain(p));

            Assert.IsTrue(reachable); // Check the assertion passed by checkng we explore beyond it
        }

        [Test()]
        public void concreteGlobal()
        {
            bool reachable = false;
            p = LoadProgramFrom("programs/RequiresConcreteGlobal.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.BreakPointReached += checkConcrete;
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name == "now_concrete")
                    this.checkEqualityConstraint(executor, data, l => l.isBvConst && l.asBvConst.ToReadableString() == "2bv8");
                else if (data.Name == "reachable")
                    reachable = true;
                else
                    Assert.Fail("Unexpected break point \"" + data.Name + "\"");
            };
            e.Run(GetMain(p));

            Assert.IsTrue(reachable, "Did not reach last assertion"); // Check the assertion passed by checkng we explore beyond it
        }

        [Test()]
        public void concreteLocalBool()
        {
            bool reachable = false;
            p = LoadProgramFrom("programs/RequiresConcreteLocalBool.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.BreakPointReached += checkConcrete;

            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name == "now_concrete")
                    this.checkEqualityConstraint(executor, data, l => l.isBool && l.asBool);
                else if (data.Name == "reachable")
                    reachable = true;
                else
                    Assert.Fail("Unexpected break point \"" + data.Name + "\"");
            };

            e.Run(GetMain(p));

            Assert.IsTrue(reachable, "Did not reach last assertion"); // Check the assertion passed by checkng we explore beyond it
        }


    }
}

