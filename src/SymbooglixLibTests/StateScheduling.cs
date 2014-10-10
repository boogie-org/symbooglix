using Microsoft.Boogie;
using NUnit.Framework;
using System;
using System.Collections.Generic;
using System.Linq;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class StateScheduling : SymbooglixTest
    {
        private void SimpleLoop(IStateScheduler scheduler)
        {
            p = loadProgram("programs/SimpleLoop.bpl");
            e = getExecutor(p, scheduler, GetSolver());
            e.UseConstantFolding = true;

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

                var symbolicForBound = eventArgs.Previous.Symbolics.Where( s => s.Origin.IsVariable && s.Origin.AsVariable == boundsVar).First();

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
        public void ExploreOrderDFS()
        {
            p = loadProgram("programs/StateScheduleTest.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());

            var main = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First();

            var entryBlock = main.Blocks[0];
            Assert.AreEqual("entry", entryBlock.Label);

            // Collect "l<N>" blocks
            var l = new List<Block>();
            for (int index = 0; index <= 5; ++index)
            {
                l.Add(main.Blocks[index + 1]);
                Assert.AreEqual("l" + index, l[index].Label);
            }

            int changed = 0;
            e.ContextChanged += delegate(object sender, Executor.ContextChangeEventArgs eventArgs)
            {
                switch(changed)
                {
                    case 0:
                        Assert.IsTrue(eventArgs.Previous.TerminationType is TerminatedWithoutError);
                        Assert.AreSame(l[2],eventArgs.Previous.Mem.Stack[0].CurrentBlock);

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[3],eventArgs.Next.GetCurrentBlock());
                        break;
                    case 1:
                        Assert.IsTrue(eventArgs.Previous.TerminationType is TerminatedWithoutError);
                        Assert.AreSame(l[3],eventArgs.Previous.Mem.Stack[0].CurrentBlock);

                        Assert.IsFalse(eventArgs.Next.Finished());
                        Assert.AreSame(l[4],eventArgs.Next.GetCurrentBlock());
                        break;
                    case 2:
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

            Assert.AreEqual(3, changed);
        }
    }
}

