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
    public class AddIdenticalConstraint : SymbooglixTest
    {
        // FIXME: Write proper unit tests for the ConstraintManager
        [Test()]
        public void IdenticalAssert()
        {
            var p = LoadProgramFrom(@"
                procedure main()
                {
                    var x:int;
                    assume {:symbooglix_bp ""before_first""} x > 5;
                    assume {:symbooglix_bp ""after_first""} true;
                    assert {:symbooglix_bp ""before_second""} x > 5;
                    assume {:symbooglix_bp ""after_second""} true;
                }
                ", "test.bpl");

            var executor = GetExecutor(p, new DFSStateScheduler(), GetSolver(), /*useConstantFolding=*/true);
            int bpCount = 0;
            ExecutionState state = null;
            executor.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs e)
            {
                if (state != null)
                    Assert.AreSame(state, executor.CurrentState);
                switch (e.Name)
                {
                    case "before_first":
                        Assert.AreEqual(0, executor.CurrentState.Constraints.Count);
                        break;
                    case "after_first":
                        Assert.AreEqual(1, executor.CurrentState.Constraints.Count);
                        break;
                    case "before_second":
                        Assert.AreEqual(1, executor.CurrentState.Constraints.Count);
                        break;
                    case "after_second":
                        // We shouldn't add the same constraint twice so we should only see one constraint
                        Assert.AreEqual(1, executor.CurrentState.Constraints.Count);
                        break;
                    default:
                        Assert.Fail("Hit unexpected break point {0}", e.Name);
                        break;
                }
                ++bpCount;
            };

            executor.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs e)
            {
                Assert.AreEqual(1, e.State.Constraints.Count);
            };

            executor.Run(GetMain(p));
            Assert.AreEqual(0, executor.Statistics.ForkCount);
            Assert.AreEqual(4, bpCount);
        }

        [Test()]
        public void SimilarAssert()
        {
            var p = LoadProgramFrom(@"
                procedure main()
                {
                    var x:int;
                    assume {:symbooglix_bp ""before_first""} x > 5;
                    assume {:symbooglix_bp ""after_first""} true;
                    assert {:symbooglix_bp ""before_second""} x > 4;
                    assume {:symbooglix_bp ""after_second""} true;
                }
                ", "test.bpl");

            var executor = GetExecutor(p, new DFSStateScheduler(), GetSolver(), /*useConstantFolding=*/true);
            int bpCount = 0;
            ExecutionState state = null;
            executor.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs e)
            {
                if (state != null)
                    Assert.AreSame(state, executor.CurrentState);

                switch (e.Name)
                {
                    case "before_first":
                        Assert.AreEqual(0, executor.CurrentState.Constraints.Count);
                        break;
                    case "after_first":
                        Assert.AreEqual(1, executor.CurrentState.Constraints.Count);
                        break;
                    case "before_second":
                        Assert.AreEqual(1, executor.CurrentState.Constraints.Count);
                        break;
                    case "after_second":
                        Assert.AreEqual(2, executor.CurrentState.Constraints.Count);
                        break;
                    default:
                        Assert.Fail("Hit unexpected break point {0}", e.Name);
                        break;
                }
                ++bpCount;
            };

            executor.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs e)
            {
                Assert.AreEqual(2, e.State.Constraints.Count);
            };

            executor.Run(GetMain(p));
            Assert.AreEqual(0, executor.Statistics.ForkCount);
            Assert.AreEqual(4, bpCount);
        }
    }
}

