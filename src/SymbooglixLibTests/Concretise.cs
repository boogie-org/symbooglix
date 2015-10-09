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
using System.Diagnostics;
using System.Linq;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Concretise : SymbooglixTest
    {
        public int hits = 0;

        [SetUp()]
        public void Init()
        {
            p = LoadProgramFrom("programs/Concretise.bpl");
            e = GetExecutor(p);
        }

        public void checkConcrete(Object executor, Executor.BreakPointEventArgs eventArgs)
        {
            if (eventArgs.Name == "entry")
            {
                ++hits;

                // Check globals are symbolic
                foreach (Variable V in e.CurrentState.Mem.Globals.Keys)
                    Assert.IsTrue(e.IsSymbolic(V));

                // Check globals are symbolic
                foreach (Variable V in e.CurrentState.GetCurrentStackFrame().Locals.Keys)
                    Assert.IsTrue(e.IsSymbolic(V));

                return;
            }

            Assert.AreEqual(1, hits);
            Assert.AreEqual("now_concrete", eventArgs.Name);
            ++hits;

            // Check "a" is now concrete
            Variable varA = e.CurrentState.GetInScopeVariableAndExprByName("a").Key;
            Assert.IsFalse(e.IsSymbolic(varA));

            // Check "x" is now concrete
            Variable varX = e.CurrentState.GetInScopeVariableAndExprByName("x").Key;
            Assert.IsFalse(e.IsSymbolic(varX));

            // Check "y" is still symbolic
            Variable varY = e.CurrentState.GetInScopeVariableAndExprByName("y").Key;
            Assert.IsTrue(e.IsSymbolic(varY));
        }
       

        [Test()]
        public void Run()
        {
            e.BreakPointReached += checkConcrete;
            e.Run(GetMain(p));
            Assert.AreEqual(2, hits);
        }

        [Test()]
        public void RequiresEqualityConstraintBool()
        {
            p = LoadProgramFrom(@"
                procedure main(p1:bool, p2:bool)
                requires (p1 == true);
                requires (p2 == false);
                {
                    assert {:symbooglix_bp ""entry""} true;
                    assert p1 == true;
                    assert p2 == false;
                }
                ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            int bpCounter = 0;
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArgs)
            {
                ++bpCounter;
                switch (eventArgs.Name)
                {
                    case "entry":
                        // Check that the arguments to main() are concrete
                        var p1 = e.CurrentState.GetInScopeVariableAndExprByName("p1");
                        Assert.IsNotNull(ExprUtil.IsTrue(p1.Value));
                        var p2 = e.CurrentState.GetInScopeVariableAndExprByName("p2");
                        Assert.IsNotNull(ExprUtil.IsFalse(p2.Value));
                        break;
                    default:
                        Assert.Fail("Unexpected break point");
                        break;
                }
            };

            var tc = new TerminationCounter();
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(1, bpCounter);
            Assert.AreEqual(1, tc.Sucesses);
            Assert.AreEqual(0, tc.NumberOfFailures);
        }

        [Test()]
        public void RequiresEqualityConstraintBV()
        {
            p = LoadProgramFrom(@"
                var g:bv32;
                procedure main()
                modifies g;
                requires (g == 0bv32);
                {
                    assert {:symbooglix_bp ""entry""} true;
                    assert g == 0bv32;
                }
                ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            int bpCounter = 0;
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArgs)
            {
                ++bpCounter;
                switch (eventArgs.Name)
                {
                    case "entry":
                        // Check that the global "g" is concrete
                        var p1 = e.CurrentState.GetInScopeVariableAndExprByName("g");
                        var asLit = ExprUtil.AsLiteral(p1.Value);
                        Assert.IsNotNull(asLit);
                        Assert.IsTrue(asLit.isBvConst);
                        Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(0), asLit.asBvConst.Value);
                        Assert.AreEqual(32, asLit.asBvConst.Bits);
                        break;
                    default:
                        Assert.Fail("Unexpected break point");
                        break;
                }
            };

            var tc = new TerminationCounter();
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(1, bpCounter);
            Assert.AreEqual(1, tc.Sucesses);
            Assert.AreEqual(0, tc.NumberOfFailures);
        }

        [Test()]
        public void RequiresEqualityConcretisesOldExpr()
        {
            p = LoadProgramFrom(@"
                var g:int;
                procedure main()
                modifies g;
                requires g == 0;
                {
                    // At this point make sure ""g"" is concrete but
                    // also make sure that the old(g) is also concrete
                    assert {:symbooglix_bp ""check""} true;
                    g := 2;
                    assert old(g + 1 -1) == 0;
                }
                ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            int bpCounter = 0;
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArgs)
            {
                ++bpCounter;
                switch (eventArgs.Name)
                {
                    case "check":
                        // Check that the global "g" is concrete
                        var p1 = e.CurrentState.GetInScopeVariableAndExprByName("g");
                        var asLit = ExprUtil.AsLiteral(p1.Value);
                        Assert.IsNotNull(asLit);
                        Assert.IsTrue(asLit.isBigNum);
                        Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(0), asLit.asBigNum);

                        // Now check that old expr for "g" also was concretised
                        var oldVars = e.CurrentState.GetCurrentStackFrame().Impl.GetOldExprVariables();
                        Assert.AreEqual(1, oldVars.Count);
                        var gVariable = oldVars[0];
                        Assert.AreEqual("g", gVariable.Name);
                        var oldExprForG = e.CurrentState.GetCurrentStackFrame().OldGlobals[gVariable];
                        var oldExprForGAsLit = ExprUtil.AsLiteral(oldExprForG);
                        Assert.IsNotNull(oldExprForGAsLit);
                        Assert.IsTrue(oldExprForGAsLit.isBigNum);
                        Assert.AreEqual(Microsoft.Basetypes.BigNum.ZERO, oldExprForGAsLit.asBigNum);

                        break;
                    default:
                        Assert.Fail("Unexpected break point");
                        break;
                }
            };

            var tc = new TerminationCounter();
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(1, bpCounter);
            Assert.AreEqual(1, tc.Sucesses);
            Assert.AreEqual(0, tc.NumberOfFailures);
        }


    }
}

