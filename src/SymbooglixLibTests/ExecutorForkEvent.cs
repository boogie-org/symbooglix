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
    public class ExecutorForkEvent : SymbooglixTest
    {
        [TestCase(false)]
        [TestCase(true)]
        public void ForkAtGoTo(bool useLookAhead)
        {
            p = LoadProgramFrom(@"
                    const g:int;
                    procedure main()
                    {
                        entry:
                            goto foo, bar;
                        foo:
                            assume g == 1;
                            return;
                        bar:
                            assume g > 1;
                            return;
                    }
                    " , "test.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = useLookAhead;
            int forkCounter = 0;
            bool hitGoto = false;
            e.ForkOccurred += delegate(object sender, Executor.ForkEventArgs e) {
                forkCounter += 1;
                Assert.AreNotSame(e.Child, e.Parent);
                Assert.IsTrue(e.Parent.Id + 1 == e.Child.Id);
                // FIXME: This doesn't work with the global id value
                // Assert.AreEqual(e.Parent.Id, 0);
                // Assert.AreEqual(e.Child.Id, 1);
                Assert.AreSame(e.Parent.GetCurrentStackFrame().Impl, e.Child.GetCurrentStackFrame().Impl);
                Assert.AreSame(e.Parent.GetCurrentBlock(), e.Child.GetCurrentBlock());
                Assert.IsInstanceOf<Microsoft.Boogie.GotoCmd>(e.Parent.GetCurrentStackFrame().CurrentInstruction.Current);
                Assert.AreSame(e.Parent.GetCurrentStackFrame().CurrentInstruction.Current, e.Child.GetCurrentStackFrame().CurrentInstruction.Current);
                hitGoto = true;
            };
            e.Run(GetMain(p));
            Assert.AreEqual(forkCounter, 1);
            Assert.IsTrue(hitGoto);
        }
    }
}
