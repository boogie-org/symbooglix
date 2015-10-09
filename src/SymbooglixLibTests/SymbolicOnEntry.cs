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

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class SymbolicOnEntry : SymbooglixTest
    {
        [SetUp()]
        public void Init()
        {
            p = LoadProgramFrom("programs/SymbolicOnEntry.bpl");
            e = GetExecutor(p);
        }

        [Test()]
        public void GlobalsAreSymbolic()
        {
            e.BreakPointReached += delegate(Object executor, Executor.BreakPointEventArgs eventArgs)
            {
                Assert.IsTrue(eventArgs.Name == "entry");
                e.CurrentState.DumpStackTrace();
                // Check that all globals are symbolic
                foreach (GlobalVariable GV in e.CurrentState.Mem.Globals.Keys)
                {
                    Assert.IsTrue(e.IsSymbolic(GV));
                }
            };
            e.Run(GetMain(p));
        }

        [Test()]
        public void LocalsAreSymbolic()
        {
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                Assert.IsTrue(data.Name == "entry");
                e.CurrentState.DumpStackTrace();
                // Check that all locals are symbolic
                foreach (Variable LV in e.CurrentState.GetCurrentStackFrame().Locals.Keys)
                {
                    Assert.IsTrue(e.IsSymbolic(LV));
                }

            };
            e.Run(GetMain(p));
        }


    }
}

