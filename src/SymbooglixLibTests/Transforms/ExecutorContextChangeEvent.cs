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
    public class ExecutorContextChangeEvent : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = LoadProgramFrom("programs/GotoMultiplePaths.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            int count = 0;
            e.ContextChanged += delegate(object sender, Executor.ContextChangeEventArgs contextChangeEventArgs)
            {
                ++count;
            };

            e.Run(GetMain(p));

            Assert.AreEqual(2, count);
        }
    }
}

