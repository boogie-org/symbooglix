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
namespace SymbooglixLibTests
{
    [TestFixture()]
    public class ExecutorTransferBBEvent : SymbooglixTest
    {
        [TestCase(false)]
        [TestCase(true)]
        public void GotoSingleTarget(bool useLookAhead)
        {
            p = LoadProgramFrom(@"
                    const g:int;
                    procedure main()
                    {
                        entry:
                            goto foo;
                        foo:
                            assume g == 1;
                            goto bar;
                        bar:
                            return;
                    }
                    " , "test.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = useLookAhead;
            int transferCounter = 0;
            e.BasicBlockChanged += delegate(object sender, Executor.TransferToBlockEventArgs eventInfo) {
                Assert.AreSame(e.CurrentState, eventInfo.State);
                switch (transferCounter) {
                    case 0:
                        Assert.AreEqual("entry", eventInfo.PreviousBlock.Label);
                        Assert.AreEqual("foo", eventInfo.NewBlock.Label);
                    break;
                    case 1:
                        Assert.AreEqual("foo", eventInfo.PreviousBlock.Label);
                        Assert.AreEqual("bar", eventInfo.NewBlock.Label);
                    break;
                    default:
                        Assert.Fail("Unexpected counter value");
                        break;
                }
                ++transferCounter;
            };
            e.Run(GetMain(p));
            Assert.AreEqual(2, transferCounter);
        }
    }
}
