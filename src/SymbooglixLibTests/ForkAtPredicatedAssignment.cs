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
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class ForkAtPredicatedAssignment : SymbooglixTest
    {
        private void Run(int expectedFailures, int expectedTerminatedStates, EventHandler<Executor.BreakPointEventArgs> bph=null)
        {
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver(), /*useConstantFolding=*/true);
            e.UseForkAtPredicatedAssign = true;
            var tc = new TerminationCounter();
            tc.Connect(e);

            int bphCounter = 0;
            if (bph != null)
            {
                e.BreakPointReached += bph;
                e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArgs)
                {
                    ++bphCounter;
                };
            }

            e.Run(GetMain(p));
            Assert.AreEqual(expectedFailures, tc.NumberOfFailures);
            Assert.AreEqual(expectedTerminatedStates, tc.NumberOfTerminatedStates);
            Assert.AreEqual(expectedTerminatedStates -1, e.Statistics.ForkCount);
            if (bph != null)
                Assert.IsFalse(bphCounter == 0);
        }

        [Test()]
        public void FollowThen()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var a:int;
                    var b:int;
                    var old_b:int;
                    old_b := b;
                    assume a > 0;
                    b := if a > 0 then 1 else b;
                    assert {:symbooglix_bp ""follow_then""} b == 1;
                }
                ", "test.bpl");
            Run(0, 1, (object sender, Executor.BreakPointEventArgs e) =>
            {
                Assert.AreEqual("follow_then", e.Name);
                Executor executor = sender as Executor;
                Assert.IsNotNull(executor);
                var pair = executor.CurrentState.GetInScopeVariableAndExprByName("b");
                Assert.IsNotNull(ExprUtil.AsLiteral(pair.Value));
                Assert.AreEqual("1", pair.Value.ToString());
            });
        }

        [Test()]
        public void FollowElse()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var a:int;
                    var b:int;
                    var old_b:int;
                    old_b := b;
                    assume a < 0;
                    b := if a > 0 then 1 else b;
                    assert {:symbooglix_bp ""follow_else""} b == old_b;
                }
                ", "test.bpl");
            Run(0, 1, (object sender, Executor.BreakPointEventArgs e) => 
            {
                Assert.AreEqual("follow_else", e.Name);
                Executor executor = sender as Executor;
                Assert.IsNotNull(executor);
                var pair = executor.CurrentState.GetInScopeVariableAndExprByName("b");
                var id = ExprUtil.AsIdentifer(pair.Value); 
                Assert.IsNotNull(id);
                Assert.IsInstanceOf<SymbolicVariable>(id.Decl);
            });
        }

        [Test()]
        public void FollowBoth()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var a:int;
                    var b:int;
                    var old_b:int;
                    old_b := b;
                    b := if a > 0 then 1 else b;
                }
                ", "test.bpl");
            Run(0, 2);
        }

        [Test()]
        public void FollowBothElseAssertFail()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var a:int;
                    var b:int;
                    var old_b:int;
                    old_b := b;
                    b := if a > 0 then 1 else b;
                    assert b == old_b;
                }
                ", "test.bpl");
            Run(1, 3);
        }

        [Test()]
        public void FollowBothThenAssertFail()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var a:int;
                    var b:int;
                    var old_b:int;
                    old_b := b;
                    b := if a > 0 then 1 else b;
                    assert b == 1;
                }
                ", "test.bpl");
            Run(1, 3);
        }
    }
}

