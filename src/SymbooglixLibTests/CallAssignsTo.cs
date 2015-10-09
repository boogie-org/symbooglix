//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using NUnit.Framework;
using Microsoft.Basetypes;
using Microsoft.Boogie;
using Symbooglix;
using System;
using System.Linq;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class CallAssignsTo : SymbooglixTest
    {
        IExprBuilder Builder;
        public CallAssignsTo()
        {
            Builder = new SimpleExprBuilder(/*immutable=*/ true);
        }

        [Test()]
        public void Global()
        {
            p = LoadProgramFrom("programs/CallAssignsToGlobal.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            bool checkg = false;
            bool checkg2 = false;

            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name != "checkg")
                    return;

                checkg = true;
                var gTuple = e.CurrentState.GetInScopeVariableAndExprByName("g");
                Assert.IsInstanceOf<LiteralExpr>(gTuple.Value);
                Assert.IsTrue((gTuple.Value as LiteralExpr).isBigNum);
                Assert.AreEqual(BigNum.FromInt(2), (gTuple.Value as LiteralExpr).asBigNum);

            };

            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name != "checkg2")
                    return;

                checkg2 = true;

                // The symbolic assigned to g2 should have a constraint that says it is equal to 3
                var g2Tuple = e.CurrentState.GetInScopeVariableAndExprByName("g2");
                var g2Expr = g2Tuple.Value;
                Assert.IsTrue(e.IsSymbolic(g2Tuple.Key));

                Assert.IsInstanceOf<IdentifierExpr>(g2Expr);
                Assert.IsInstanceOf<SymbolicVariable>((g2Expr as IdentifierExpr).Decl);

                var expectedConstraint = Expr.Eq(g2Expr, Builder.ConstantInt(3));
                int found = e.CurrentState.Constraints.Constraints.Where( c => c.Condition.Equals(expectedConstraint)).Count();
                Assert.AreEqual(1, found);
            };

            e.Run(GetMain(p));

            Assert.IsTrue(checkg);
            Assert.IsTrue(checkg2);
        }

        [Test()]
        public void Local()
        {
            p = LoadProgramFrom("programs/CallAssignsToLocal.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            bool checka= false;
            bool checkb = false;

            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name != "checka")
                    return;

                checka = true;
                var aTuple = e.CurrentState.GetInScopeVariableAndExprByName("a");
                Assert.IsInstanceOf<LiteralExpr>(aTuple.Value);
                Assert.IsTrue((aTuple.Value as LiteralExpr).isBigNum);
                Assert.AreEqual(BigNum.FromInt(2), (aTuple.Value as LiteralExpr).asBigNum);

            };

            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name != "checkb")
                    return;

                checkb = true;

                // The symbolic assigned to b should have a constraint that says it is equal to 3
                var bTuple = e.CurrentState.GetInScopeVariableAndExprByName("b");
                var bExpr = bTuple.Value;
                Assert.IsTrue(e.IsSymbolic(bTuple.Key));

                Assert.IsInstanceOf<IdentifierExpr>(bExpr);
                Assert.IsInstanceOf<SymbolicVariable>((bExpr as IdentifierExpr).Decl);

                var expectedConstraint = Expr.Eq(bExpr, Builder.ConstantInt(3));
                int found = e.CurrentState.Constraints.Constraints.Where( c => c.Condition.Equals(expectedConstraint)).Count();
                Assert.AreEqual(1, found);
            };

            e.Run(GetMain(p));

            Assert.IsTrue(checka);
            Assert.IsTrue(checkb);
        }
    }
}

