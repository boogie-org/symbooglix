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
using Microsoft.Boogie;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class EnterAndLeaveProcedureImplementationEvents : SymbooglixTest
    {
        [Test()]
        public void enterImplementationEvent()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var x:int;
                    call foo(x);
                }

                procedure foo(x:int)
                {

                }
                ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            int counter = 0;
            e.ImplementationEntered += delegate(object sender, Executor.EnterImplementationEventArgs eventArgs)
            {
                switch (counter)
                {
                    case 0:
                        Assert.AreEqual("main", eventArgs.Impl.Name);
                        Assert.IsNull(eventArgs.Args);
                        break;
                    case 1:
                        Assert.AreEqual("foo", eventArgs.Impl.Name);
                        Assert.AreEqual(1, eventArgs.Args.Count);
                        break;
                    default:
                        Assert.Fail("Unexpected implementation");
                        break;
                }
                ++counter;
            };
            e.Run(GetMain(p));
            Assert.AreEqual(2, counter);
        }

        [Test()]
        public void leaveImplementationEvent()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var x:int;
                    call foo(x);
                }

                procedure foo(x:int)
                {

                }
                ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            int counter = 0;
            e.ImplementationLeft += delegate(object sender, Executor.LeaveImplementationEventArgs eventArgs)
            {
                switch (counter)
                {
                    case 1:
                        Assert.AreEqual("main", eventArgs.Impl.Name);
                        break;
                    case 0:
                        Assert.AreEqual("foo", eventArgs.Impl.Name);
                        break;
                    default:
                        Assert.Fail("Unexpected implementation");
                        break;
                }
                ++counter;
            };
            e.Run(GetMain(p));
            Assert.AreEqual(2, counter);
        }

        [Test()]
        public void enterProcedureEvent()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var x:int;
                    call foo(x);
                }

                procedure foo(x:int);
                ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            int counter = 0;
            e.ProcedureEntered += delegate(object sender, Executor.EnterProcedureEventArgs eventArgs)
            {
                switch (counter)
                {
                    case 0:
                        Assert.AreEqual("foo", eventArgs.Proc.Name);
                        Assert.AreEqual(1, eventArgs.Args.Count);
                        break;
                    default:
                        Assert.Fail("Unexpected procedure");
                        break;
                }
                ++counter;
            };
            e.Run(GetMain(p));
            Assert.AreEqual(1, counter);
        }

        [Test()]
        public void leaveProcedureEvent()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var x:int;
                    call foo(x);
                }

                procedure foo(x:int);
                ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            int counter = 0;
            e.ProcedureLeft += delegate(object sender, Executor.LeaveProcedureEventArgs eventArgs)
            {
                switch (counter)
                {
                    case 0:
                        Assert.AreEqual("foo", eventArgs.Proc.Name);
                        break;
                    default:
                        Assert.Fail("Unexpected procedure");
                        break;
                }
                ++counter;
            };
            e.Run(GetMain(p));
            Assert.AreEqual(1, counter);
        }
    }
}

