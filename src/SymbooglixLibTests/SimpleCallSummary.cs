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
using System;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using System.Linq;
using System.Collections.Generic;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class SimpleCallSummary : SymbooglixTest
    {
        IExprBuilder Builder;

        private void Init()
        {
            p = LoadProgramFrom("programs/SimpleCallSummary.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            Builder = new SimpleExprBuilder(/*immutable=*/ true);
        }

        [Test()]
        public void NoFailures()
        {
            Init();

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(1, counter.Sucesses);
            Assert.AreEqual(0, counter.NumberOfFailures);
        }

        [Test()]
        public void ModifiesSetOrigin()
        {
            Init();

            bool hitExpectedBreakPoint = false;
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name != "cmodset")
                    return;

                hitExpectedBreakPoint = true;

                // Check that global variable c is symbolic and the origin is from bar()'s modset
                var tuple = e.CurrentState.GetInScopeVariableAndExprByName("c");
                var cVar = tuple.Key;
                Assert.IsInstanceOf<GlobalVariable>(cVar);
                var cExpr = tuple.Value;
                Assert.IsInstanceOf<IdentifierExpr>(cExpr);
                Assert.IsInstanceOf<SymbolicVariable>((cExpr as IdentifierExpr).Decl);
                var cSymbolicVar = (cExpr as IdentifierExpr).Decl as SymbolicVariable;
                Assert.IsTrue(cSymbolicVar.Origin.IsModifiesSet);

                var barProcedure = p.TopLevelDeclarations.OfType<Procedure>().Where( proc => proc.Name == "bar").First();
                Assert.AreSame((cSymbolicVar.Origin.AsModifiesSet).Proc, barProcedure);
            };

            e.Run(GetMain(p));

            Assert.IsTrue(hitExpectedBreakPoint);
        }

        [Test(), Ignore("FIXME: Need way of finding symbolics for a variable")]
        public void RequiresXMinusOne()
        {
            Init();

            bool hitExpectedBreakPoint = false;
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name != "cmodset")
                    return;

                hitExpectedBreakPoint = true;

                // Check for "requires x > -1" constraint
                var xTuple = e.CurrentState.GetInScopeVariableAndExprByName("x");
                var xVar = xTuple.Key;
                // Find the symbolic associated with this variable

                // FIXME: Broken
                //var symbolicForX = e.CurrentState.Symbolics.Where( s => s.Origin.IsVariable && s.Origin.AsVariable == xVar).First();
                SymbolicVariable symbolicForX = null; // Just so it compiles

                // FIXME: Move constant construction functions to utility so can be shared across tests.
                var expectedConstraint = Expr.Gt(symbolicForX.Expr, Expr.Neg(Builder.ConstantInt(1)));

                int hasConstraint = e.CurrentState.Constraints.Constraints.Where( c => c.Condition.Equals(expectedConstraint)).Count();
                Assert.AreEqual(1, hasConstraint);
            };

            e.Run(GetMain(p));

            Assert.IsTrue(hitExpectedBreakPoint);
        }

        [Test()]
        public void RequiresA()
        {
            Init();

            bool hitExpectedBreakPoint = false;
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name != "cmodset")
                    return;

                hitExpectedBreakPoint = true;

                // Check for "requires a > 0" constraint which is "2 > 0" where 2 is the value of a
                var aTuple = e.CurrentState.GetInScopeVariableAndExprByName("a");
                var aExpr = aTuple.Value;
                Assert.IsInstanceOf<LiteralExpr>(aExpr);
                Assert.AreEqual(BigNum.FromInt(2), (aExpr as LiteralExpr).asBigNum);
                var expectedConstraint3 = Expr.Gt(aExpr, Builder.ConstantInt(0));
                int hasConstraint3 = e.CurrentState.Constraints.Constraints.Where( c => c.Condition.Equals(expectedConstraint3)).Count();
                Assert.AreEqual(1, hasConstraint3);


            };

            e.Run(GetMain(p));

            Assert.IsTrue(hitExpectedBreakPoint);
        }

        [Test()]
        public void ConstrainReturnValue()
        {
            Init();

            bool hitExpectedBreakPoint = false;
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name != "cmodset")
                    return;

                hitExpectedBreakPoint = true;

                var barProcedure = p.TopLevelDeclarations.OfType<Procedure>().Where( proc => proc.Name == "bar").First();
                // Check for "ensures r > 0" constraint which is assigned to b
                var bTuple = e.CurrentState.GetInScopeVariableAndExprByName("b");
                var bExpr = bTuple.Value;
                Assert.IsInstanceOf<IdentifierExpr>(bExpr);
                Assert.IsInstanceOf<SymbolicVariable>((bExpr as IdentifierExpr).Decl);
                var symbolicForB = (bExpr as IdentifierExpr).Decl as SymbolicVariable;
                Assert.IsTrue(symbolicForB.Origin.IsVariable);
                var rVar = barProcedure.OutParams[0];
                Assert.AreEqual(symbolicForB.Origin.AsVariable, rVar);
                var expectedConstraint2 = Expr.Gt(symbolicForB.Expr, Builder.ConstantInt(0));
                int hasConstraint2 = e.CurrentState.Constraints.Constraints.Where( c => c.Condition.Equals(expectedConstraint2)).Count();
                Assert.AreEqual(1, hasConstraint2);

            };

            e.Run(GetMain(p));

            Assert.IsTrue(hitExpectedBreakPoint);
        }
    }
}

