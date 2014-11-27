﻿using Microsoft.Boogie;
using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Assignment : SymbooglixTest
    {
        [Test()]
        public void SimpleConcreteAssignment()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var x:int;
                    assert {:symbooglix_bp ""before""} true;
                    x := 5;
                    assert {:symbooglix_bp ""after""} true;
                }
            ", "file.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            int count = 0;
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArgs)
            {
                switch (eventArgs.Name)
                {
                    case "before":
                        var vAndExpr = e.CurrentState.GetInScopeVariableAndExprByName("x");
                        Assert.IsInstanceOf<IdentifierExpr>(vAndExpr.Value);
                        Assert.IsInstanceOf<SymbolicVariable>((vAndExpr.Value as IdentifierExpr).Decl);
                        break;
                    case "after":
                        vAndExpr = e.CurrentState.GetInScopeVariableAndExprByName("x");
                        Assert.IsInstanceOf<LiteralExpr>(vAndExpr.Value);
                        var literal = vAndExpr.Value as LiteralExpr;
                        Assert.IsTrue(literal.isBigNum);
                        Assert.AreEqual(5, literal.asBigNum.ToInt);
                        break;
                    default:
                        Assert.Fail("unrecognised breakpoint");
                        break;
                }
                ++count;
            };
            e.Run(GetMain(p));
            Assert.AreEqual(2, count);
        }

        [Test()]
        public void SimpleSymbolicAssigment()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var x:int;
                    assert {:symbooglix_bp ""before""} true;
                    x :=  x + x;
                    assert {:symbooglix_bp ""after""} true;
                }
            ", "file.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            int count = 0;
            IdentifierExpr symbolic = null;
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArgs)
            {
                switch (eventArgs.Name)
                {
                    case "before":
                        var vAndExpr = e.CurrentState.GetInScopeVariableAndExprByName("x");
                        Assert.IsInstanceOf<IdentifierExpr>(vAndExpr.Value);
                        Assert.IsInstanceOf<SymbolicVariable>((vAndExpr.Value as IdentifierExpr).Decl);
                        symbolic = vAndExpr.Value as IdentifierExpr;
                        break;
                    case "after":
                        Assert.IsNotNull(symbolic);
                        vAndExpr = e.CurrentState.GetInScopeVariableAndExprByName("x");
                        Assert.IsInstanceOf<NAryExpr>(vAndExpr.Value);
                        Assert.IsInstanceOf<BinaryOperator>((vAndExpr.Value as NAryExpr).Fun);
                        Assert.AreEqual(BinaryOperator.Opcode.Add, (( vAndExpr.Value as NAryExpr).Fun as BinaryOperator).Op);
                        Assert.AreEqual(symbolic.Name + " + " + symbolic.Name, vAndExpr.Value.ToString());
                        break;
                    default:
                        Assert.Fail("unrecognised breakpoint");
                        break;
                }
                ++count;
            };
            e.Run(GetMain(p));
            Assert.AreEqual(2, count);
        }

        [Test()]
        public void SimpleMapAssigment()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var x:[bool]int;
                    assert {:symbooglix_bp ""before""} true;
                    x[true] :=  8;
                    assert {:symbooglix_bp ""after""} true;
                }
            ", "file.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            int count = 0;
            IdentifierExpr symbolic = null;
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArgs)
            {
                switch (eventArgs.Name)
                {
                    case "before":
                        var vAndExpr = e.CurrentState.GetInScopeVariableAndExprByName("x");
                        Assert.IsInstanceOf<IdentifierExpr>(vAndExpr.Value);
                        Assert.IsInstanceOf<SymbolicVariable>((vAndExpr.Value as IdentifierExpr).Decl);
                        symbolic = vAndExpr.Value as IdentifierExpr;
                        break;
                    case "after":
                        Assert.IsNotNull(symbolic);
                        vAndExpr = e.CurrentState.GetInScopeVariableAndExprByName("x");
                        Assert.IsInstanceOf<NAryExpr>(vAndExpr.Value);
                        Assert.IsInstanceOf<MapStore>((vAndExpr.Value as NAryExpr).Fun);
                        Assert.AreEqual(symbolic.Name + "[true := 8]", vAndExpr.Value.ToString());
                        break;
                    default:
                        Assert.Fail("unrecognised breakpoint");
                        break;
                }
                ++count;
            };
            e.Run(GetMain(p));
            Assert.AreEqual(2, count);
        }
    }
}
