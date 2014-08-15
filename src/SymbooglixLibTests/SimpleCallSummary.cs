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
        private void Init()
        {
            p = loadProgram("programs/SimpleCallSummary.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
        }

        [Test()]
        public void NoFailures()
        {
            Init();

            var counter = new TerminationCounter();
            counter.Connect(e);
            e.Run(getMain(p));
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
                Assert.IsInstanceOfType(typeof(GlobalVariable), cVar);
                var cExpr = tuple.Value;
                Assert.IsInstanceOfType(typeof(IdentifierExpr), cExpr);
                Assert.IsInstanceOfType(typeof(SymbolicVariable), (cExpr as IdentifierExpr).Decl);
                var cSymbolicVar = (cExpr as IdentifierExpr).Decl as SymbolicVariable;
                Assert.IsTrue(cSymbolicVar.Origin.IsModifiesSet);

                var barProcedure = p.TopLevelDeclarations.OfType<Procedure>().Where( proc => proc.Name == "bar").First();
                Assert.AreSame((cSymbolicVar.Origin.AsModifiesSet).Proc, barProcedure);
            };

            e.Run(getMain(p));

            Assert.IsTrue(hitExpectedBreakPoint);
        }

        [Test()]
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
                var symbolicForX = e.CurrentState.Symbolics.Where( s => s.Origin.IsVariable && s.Origin.AsVariable == xVar).First();

                // FIXME: Move constant construction functions to utility so can be shared across tests.
                // FIXME: Add negate to Boogie.
                var negatedOne = new NAryExpr(Token.NoToken, new UnaryOperator(Token.NoToken, UnaryOperator.Opcode.Neg), new List<Expr> { ConstantFoldingTests.TestBase.getConstantInt(1) });
                var expectedConstraint = Expr.Gt(symbolicForX.Expr, negatedOne);
                e.CurrentState.Constraints.Constraints[2].Equals(expectedConstraint);

                int hasConstraint = e.CurrentState.Constraints.Constraints.Where( c => c.Equals(expectedConstraint)).Count();
                Assert.AreEqual(1, hasConstraint);
            };

            e.Run(getMain(p));

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
                Assert.IsInstanceOfType(typeof(LiteralExpr), aExpr);
                Assert.AreEqual(BigNum.FromInt(2), (aExpr as LiteralExpr).asBigNum);
                var expectedConstraint3 = Expr.Gt(aExpr, ConstantFoldingTests.TestBase.getConstantInt(0));
                int hasConstraint3 = e.CurrentState.Constraints.Constraints.Where( c => c.Equals(expectedConstraint3)).Count();
                Assert.AreEqual(1, hasConstraint3);


            };

            e.Run(getMain(p));

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
                Assert.IsInstanceOfType(typeof(IdentifierExpr), bExpr);
                Assert.IsInstanceOfType(typeof(SymbolicVariable), (bExpr as IdentifierExpr).Decl);
                var symbolicForB = (bExpr as IdentifierExpr).Decl as SymbolicVariable;
                Assert.IsTrue(symbolicForB.Origin.IsVariable);
                var rVar = barProcedure.OutParams[0];
                Assert.AreEqual(symbolicForB.Origin.AsVariable, rVar);
                var expectedConstraint2 = Expr.Gt(symbolicForB.Expr, ConstantFoldingTests.TestBase.getConstantInt(0));
                int hasConstraint2 = e.CurrentState.Constraints.Constraints.Where( c => c.Equals(expectedConstraint2)).Count();
                Assert.AreEqual(1, hasConstraint2);

            };

            e.Run(getMain(p));

            Assert.IsTrue(hitExpectedBreakPoint);
        }
    }
}

