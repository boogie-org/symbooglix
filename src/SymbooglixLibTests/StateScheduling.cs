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
using System;
using System.Collections.Generic;
using System.Linq;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture(), Ignore("FIXME: Need way to easily get symbolics for a particular variable")]
    public class StateScheduling : SymbooglixTest
    {
        private void SimpleLoop(IStateScheduler scheduler)
        {
            p = LoadProgramFrom("programs/SimpleLoop.bpl");
            e = GetExecutor(p, scheduler, GetSolver(), /*useConstantFolding=*/ true);

            var main = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First();

            var boundsVar = main.InParams[0];

            var entryBlock = main.Blocks[0];
            Assert.AreEqual("entry", entryBlock.Label);

            var loopHead = main.Blocks[1];
            Assert.AreEqual("loopHead", loopHead.Label);

            var loopBody = main.Blocks[2];
            Assert.AreEqual("loopBody", loopBody.Label);
            var loopBodyAssume = loopBody.Cmds[0] as AssumeCmd;
            Assert.IsNotNull(loopBodyAssume);

            var loopExit = main.Blocks[3];
            Assert.AreEqual("loopDone", loopExit.Label);
            var loopExitAssume = loopExit.Cmds[0] as AssumeCmd;
            Assert.IsNotNull(loopExitAssume);

            var exitBlock = main.Blocks[4];
            Assert.AreEqual("exit", exitBlock.Label);

            var tc = new TerminationCounter();
            tc.Connect(e);

            int change = 1;
            int contextChangeCount = 0;
            e.ContextChanged += delegate(object sender, Executor.ContextChangeEventArgs eventArgs)
            {
                ++contextChangeCount;

                // FIXME:
                //var symbolicForBound = eventArgs.Previous.Symbolics.Where( s => s.Origin.IsVariable && s.Origin.AsVariable == boundsVar).First();
                SymbolicVariable symbolicForBound = null; // Just so we can compile

                if (change ==1)
                {
                    // FIXME: The Executor shouldn't pop the last stack frame so we can check where we terminated successfully
                    Assert.IsTrue(eventArgs.Previous.TerminationType.ExitLocation.IsTransferCmd);
                    Assert.IsTrue(eventArgs.Previous.TerminationType.ExitLocation.AsTransferCmd is ReturnCmd);
                    Assert.IsTrue(eventArgs.Previous.Finished());
                    Assert.AreEqual(3, eventArgs.Previous.Constraints.Count);
                    var exitConstraint = eventArgs.Previous.Constraints.Constraints.Where( c => c.Origin.IsCmd && c.Origin.AsCmd == loopExitAssume);
                    Assert.AreEqual(1, exitConstraint.Count());
                    Assert.AreEqual( symbolicForBound.Name + " <= 0", exitConstraint.First().Condition.ToString());

                    Assert.AreSame(loopBody, eventArgs.Next.GetCurrentBlock());
                    Assert.AreEqual(2, eventArgs.Next.Constraints.Count);
                    var bodyConstraint = eventArgs.Next.Constraints.Constraints.Where( c => c.Origin.IsCmd && c.Origin.AsCmd == loopBodyAssume);
                    Assert.AreEqual(1, bodyConstraint.Count());
                    Assert.AreEqual("0 < " + symbolicForBound.Name, bodyConstraint.First().Condition.ToString());
                }
                else if (change == 2)
                {
                    Assert.IsTrue(eventArgs.Previous.Finished());
                    Assert.AreSame(loopBody, eventArgs.Next.GetCurrentBlock());
                    Assert.AreEqual(4, eventArgs.Previous.Constraints.Count);

                    var exitConstraint = eventArgs.Previous.Constraints.Constraints.Where( c => c.Origin.IsCmd && c.Origin.AsCmd == loopExitAssume);
                    Assert.AreEqual(1, exitConstraint.Count());
                    Assert.AreEqual( symbolicForBound.Name + " <= 1", exitConstraint.First().Condition.ToString());

                    Assert.AreSame(loopBody, eventArgs.Next.GetCurrentBlock());
                    Assert.AreEqual(3, eventArgs.Next.Constraints.Count);
                    var bodyConstraints = eventArgs.Next.Constraints.Constraints.Where( c => c.Origin.IsCmd && c.Origin.AsCmd == loopBodyAssume).ToList();
                    Assert.AreEqual(2, bodyConstraints.Count());
                    Assert.AreEqual("0 < " + symbolicForBound.Name, bodyConstraints[0].Condition.ToString());
                    Assert.AreEqual("1 < " + symbolicForBound.Name, bodyConstraints[1].Condition.ToString());
                }


                ++change;
            };

            e.Run(main);
            Assert.AreEqual(3, tc.NumberOfTerminatedStates);
            Assert.AreEqual(3, tc.Sucesses);
            Assert.AreEqual(2, contextChangeCount);
        }

        [Test()]
        public void ExploreAllStatesDFS()
        {
            SimpleLoop(new DFSStateScheduler());
        }

        [Test()]
        public void ExploreAllStatesUntilTerminationBFS()
        {
            SimpleLoop(new UntilTerminationBFSStateScheduler());
        }

        [Test()]
        public void ExploreAllStatesBFS()
        {
            // TODO: SimpleLoop() assumes DFS can't use it
            //SimpleLoop(new BFSStateScheduler());
        }

        private void ExploreOrderInit(IStateScheduler scheduler, out Implementation main, out Block entryBlock, out List<Block> l)
        {
            p = LoadProgramFrom("programs/StateScheduleTest.bpl");
            e = GetExecutor(p, scheduler, GetSolver());

            main = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First();
            entryBlock = main.Blocks[0];
            Assert.AreEqual("entry", entryBlock.Label);

            // Collect "l<N>" blocks
            l = new List<Block>();
            for (int index = 0; index <= 5; ++index)
            {
                l.Add(main.Blocks[index + 1]);
                Assert.AreEqual("l" + index, l[index].Label);
            }
        }

        [Test()]
        public void ExploreOrderDFS()
        {
            List<Block> l;
            Block entryBlock;
            Implementation main;
            ExploreOrderInit(new DFSStateScheduler(), out main, out entryBlock, out l);

            int changed = 0;
            e.ContextChanged += delegate(object sender, Executor.ContextChangeEventArgs eventArgs)
            {
                switch(changed)
                {
                    case 0:
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.Previous.TerminationType);
                        Assert.AreSame(l[2],eventArgs.Previous.Mem.Stack[0].CurrentBlock);

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[3],eventArgs.Next.GetCurrentBlock());
                        break;
                    case 1:
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.Previous.TerminationType);
                        Assert.AreSame(l[3],eventArgs.Previous.Mem.Stack[0].CurrentBlock);

                        /* FIXME: At a three way branch we schedule l0, l2, l1 rather than
                         * l0, l1, l2. i.e. we aren't going left to right over the GotoCmd targets.
                         * This is because the DFSScheduler executes the last added state first so it executes the ExecutionState
                         * going to l2 before the state going to l1.
                         *
                         * I'm not sure this is desirable.
                         */
                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[2],eventArgs.Next.GetCurrentBlock());
                        break;
                    case 2:
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.Previous.TerminationType);
                        Assert.AreSame(l[2],eventArgs.Previous.GetCurrentBlock());

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[1],eventArgs.Next.GetCurrentBlock());
                        break;

                    case 3:
                        Assert.IsTrue(eventArgs.Previous.TerminationType is TerminatedWithoutError);
                        Assert.AreSame(l[4],eventArgs.Previous.Mem.Stack[0].CurrentBlock);

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[5],eventArgs.Next.GetCurrentBlock());
                        break;
                    default:
                        Assert.Fail("Too many context changes");
                        break;
                }
                ++changed;
            };

            e.Run(main);

            Assert.AreEqual(4, changed);
        }

        [Test()]
        public void ExploreOrderUntilEndBFS()
        {
            List<Block> l;
            Block entryBlock;
            Implementation main;
            ExploreOrderInit(new UntilTerminationBFSStateScheduler(), out main, out entryBlock, out l);

            // Is this actually correct?
            int changed = 0;
            e.ContextChanged += delegate(object sender, Executor.ContextChangeEventArgs eventArgs)
            {
                switch(changed)
                {
                    case 0:
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.Previous.TerminationType);
                        Assert.AreSame(l[2],eventArgs.Previous.Mem.Stack[0].CurrentBlock);

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[1],eventArgs.Next.GetCurrentBlock());
                        break;
                    case 1:
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.Previous.TerminationType);
                        Assert.AreSame(l[4],eventArgs.Previous.Mem.Stack[0].CurrentBlock);

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[2],eventArgs.Next.GetCurrentBlock());
                        break;
                    case 2:
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.Previous.TerminationType);
                        Assert.AreSame(l[2],eventArgs.Previous.GetCurrentBlock());

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[3],eventArgs.Next.GetCurrentBlock());
                        break;

                    case 3:
                        Assert.IsTrue(eventArgs.Previous.TerminationType is TerminatedWithoutError);
                        Assert.AreSame(l[3],eventArgs.Previous.Mem.Stack[0].CurrentBlock);

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[5],eventArgs.Next.GetCurrentBlock());
                        break;
                    default:
                        Assert.Fail("Too many context changes");
                        break;
                }
                ++changed;
            };

            e.Run(main);

            Assert.AreEqual(4, changed);
        }

        [Test()]
        public void ExploreOrderBFS()
        {
            List<Block> l;
            Block entryBlock;
            Implementation main;
            ExploreOrderInit(new BFSStateScheduler(), out main, out entryBlock, out l);

            int changed = 0;
            int previousStateId = 0;
            e.ContextChanged += delegate(object sender, Executor.ContextChangeEventArgs eventArgs)
            {

                switch(changed)
                {
                    case 0:
                        Assert.IsFalse(eventArgs.Previous.Finished());
                        Assert.AreSame(l[0],eventArgs.Previous.GetCurrentBlock());
                        Assert.AreEqual(1, eventArgs.Previous.ExplicitBranchDepth);

                        /* Depth 0 explored */

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[1],eventArgs.Next.GetCurrentBlock());
                        Assert.AreEqual(1, eventArgs.Next.ExplicitBranchDepth);
                        previousStateId = eventArgs.Next.Id;
                        break;
                    case 1:
                        Assert.AreEqual(previousStateId, eventArgs.Previous.Id);
                        Assert.IsFalse(eventArgs.Previous.Finished());
                        Assert.AreSame(l[4],eventArgs.Previous.GetCurrentBlock());
                        Assert.AreEqual(2, eventArgs.Previous.ExplicitBranchDepth); // Changing context because have gone deeper

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[2],eventArgs.Next.GetCurrentBlock());
                        previousStateId = eventArgs.Next.Id;
                        break;
                    case 2:
                        Assert.AreEqual(previousStateId, eventArgs.Previous.Id);
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.Previous.TerminationType);
                        Assert.AreSame(l[2],eventArgs.Previous.GetCurrentBlock());
                        Assert.AreEqual(1, eventArgs.Previous.ExplicitBranchDepth);

                        Assert.IsFalse(eventArgs.Next.Finished());
                        // Now resuming execution of initial state
                        Assert.AreSame(l[0],eventArgs.Next.GetCurrentBlock());
                        Assert.AreEqual(1, eventArgs.Next.ExplicitBranchDepth);
                        previousStateId = eventArgs.Next.Id;
                        break;
                    case 3:
                        Assert.AreEqual(previousStateId, eventArgs.Previous.Id);
                        Assert.IsFalse(eventArgs.Previous.Finished());
                        // Original state has made it to block l2
                        Assert.AreSame(l[2],eventArgs.Previous.GetCurrentBlock());
                        Assert.AreEqual(2, eventArgs.Previous.ExplicitBranchDepth); // Changing context because have gone deeper

                        /* Depth 1 explored ? */

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[5],eventArgs.Next.GetCurrentBlock());
                        Assert.AreEqual(2, eventArgs.Next.ExplicitBranchDepth);
                        previousStateId = eventArgs.Next.Id;
                        break;
                    case 4:
                        Assert.AreEqual(previousStateId, eventArgs.Previous.Id);
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.Previous.TerminationType);
                        Assert.AreSame(l[5],eventArgs.Previous.GetCurrentBlock());
                        Assert.AreEqual(2, eventArgs.Previous.ExplicitBranchDepth);

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[4], eventArgs.Next.GetCurrentBlock());
                        Assert.AreEqual(2, eventArgs.Next.ExplicitBranchDepth);
                        previousStateId = eventArgs.Next.Id;
                        break;
                    case 5:
                        Assert.AreEqual(previousStateId, eventArgs.Previous.Id);
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.Previous.TerminationType);
                        Assert.AreSame(l[4],eventArgs.Previous.GetCurrentBlock());
                        Assert.AreEqual(2, eventArgs.Previous.ExplicitBranchDepth);

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[3], eventArgs.Next.GetCurrentBlock());
                        Assert.AreEqual(2, eventArgs.Next.ExplicitBranchDepth);
                        previousStateId = eventArgs.Next.Id;
                        break;
                    case 6:
                        Assert.AreEqual(previousStateId, eventArgs.Previous.Id);
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.Previous.TerminationType);
                        Assert.AreSame(l[3],eventArgs.Previous.GetCurrentBlock());
                        Assert.AreEqual(2, eventArgs.Previous.ExplicitBranchDepth);

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[2], eventArgs.Next.GetCurrentBlock());
                        Assert.AreEqual(2, eventArgs.Next.ExplicitBranchDepth);
                        break;
                    default:
                        Assert.Fail("Too many context changes");
                        break;
                }
                ++changed;
            };

            var tc = new TerminationCounter();
            tc.Connect(e);

            e.Run(main);
            Assert.AreEqual(7, changed);
            Assert.AreEqual(5, tc.Sucesses);
            Assert.AreEqual(5, tc.NumberOfTerminatedStates);
        }

        [Test()]
        public void DepthBoundDFS()
        {
            var scheduler = new LimitExplicitDepthScheduler(new DFSStateScheduler(), 2);
            p = LoadProgramFrom("programs/SimpleLoop.bpl");
            e = GetExecutor(p, scheduler, GetSolver());

            var tc = new TerminationCounter();
            tc.Connect(e);

            e.Run(GetMain(p));

            Assert.AreEqual(3, tc.NumberOfTerminatedStates);
            Assert.AreEqual(2, tc.Sucesses);
            Assert.AreEqual(1, tc.DisallowedPathDepths);
        }

        [Test()]
        public void DepthBoundBFS()
        {
            var scheduler = new LimitExplicitDepthScheduler(new BFSStateScheduler(), 2);
            p = LoadProgramFrom("programs/SimpleLoop.bpl");
            e = GetExecutor(p, scheduler, GetSolver());

            var tc = new TerminationCounter();
            tc.Connect(e);

            e.Run(GetMain(p));

            Assert.AreEqual(3, tc.NumberOfTerminatedStates);
            Assert.AreEqual(2, tc.Sucesses);
            Assert.AreEqual(1, tc.DisallowedPathDepths);
        }

        [Test()]
        public void ExploreOrderLoopEscapingScheduler()
        {
            var scheduler = new LoopEscapingScheduler(new DFSStateScheduler());
            p = LoadProgramFrom("programs/TestLoopEscaping.bpl");

            // Get the blocks we need to refer to
            var main = GetMain(p);
            var loopBodyBlock = main.Blocks.Where(b => b.Label == "anon2_LoopBody").First();
            var loopDoneBlock = main.Blocks.Where(b => b.Label == "anon2_LoopDone").First();

            e = GetExecutor(p, scheduler, GetSolver(), /*useConstantFolding=*/ true);

            var tc = new TerminationCounter();
            tc.Connect(e);

            int changed = 0;
            e.ContextChanged += delegate(object sender, Executor.ContextChangeEventArgs eventArgs)
            {
                switch (changed)
                {
                    case 0:
                        Assert.AreSame(loopBodyBlock, eventArgs.Previous.GetCurrentBlock());
                        Assert.IsFalse(eventArgs.Previous.Finished());

                        Assert.AreSame(loopDoneBlock, eventArgs.Next.GetCurrentBlock());
                        Assert.AreEqual(0, GetLoopCounter(eventArgs.Next));
                        Assert.IsFalse(eventArgs.Next.Finished());
                        break;
                    case 1:
                        Assert.AreSame(loopDoneBlock, eventArgs.Previous.GetCurrentBlock());
                        Assert.AreEqual(0, GetLoopCounter(eventArgs.Previous));
                        Assert.IsTrue(eventArgs.Previous.Finished());
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.Previous.TerminationType);

                        Assert.AreSame(loopBodyBlock, eventArgs.Next.GetCurrentBlock());
                        Assert.AreEqual(0, GetLoopCounter(eventArgs.Next));
                        Assert.IsFalse(eventArgs.Next.Finished());
                        break;
                    case 2:
                        Assert.AreSame(loopBodyBlock, eventArgs.Previous.GetCurrentBlock());
                        Assert.AreEqual(1, GetLoopCounter(eventArgs.Next));
                        Assert.IsFalse(eventArgs.Next.Finished());

                        Assert.AreSame(loopDoneBlock, eventArgs.Next.GetCurrentBlock());
                        Assert.AreEqual(1, GetLoopCounter(eventArgs.Next));
                        Assert.IsFalse(eventArgs.Next.Finished());
                        break;
                    case 3:
                        Assert.AreSame(loopDoneBlock, eventArgs.Previous.GetCurrentBlock());
                        Assert.AreEqual(1, GetLoopCounter(eventArgs.Previous));
                        Assert.IsTrue(eventArgs.Previous.Finished());
                        Assert.IsInstanceOf<TerminatedWithoutError>(eventArgs.Previous.TerminationType);

                        // About to execute last possible execution of loop body
                        Assert.AreSame(loopBodyBlock, eventArgs.Next.GetCurrentBlock());
                        Assert.AreEqual(1, GetLoopCounter(eventArgs.Next));
                        Assert.IsFalse(eventArgs.Next.Finished());
                        break;
                    default:
                        Assert.Fail("Too many context changes");
                        break;

                }
                ++changed;
            };

            e.Run(main);

            Assert.AreEqual(3, tc.NumberOfTerminatedStates);
            Assert.AreEqual(3, tc.Sucesses);
            Assert.AreEqual(4, changed);
        }


        private int GetLoopCounter(ExecutionState state)
        {
            var pair = state.GetInScopeVariableAndExprByName("counter");

            Assert.IsInstanceOf<LiteralExpr>(pair.Value);

            var value = pair.Value as LiteralExpr;
            Assert.IsTrue(value.isBigNum);
            return value.asBigNum.ToIntSafe;
        }
    }

}

