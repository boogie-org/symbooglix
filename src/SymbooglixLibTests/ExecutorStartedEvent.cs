//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2017 Daniel Liew
//
// This file is licensed under the MIT license.
// See LICENSE.txt for details.
//------------------------------------------------------------------------------
using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class ExecutorStartedEvent : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = LoadProgramFrom("programs/GotoSinglePath.bpl");
            e = GetExecutor(p);

            bool started = false;
            e.ExecutorStarted += delegate(object sender, Executor.ExecutorStartedArgs executorStartedArgs)
            {
                started = true;
            };

            e.Run(GetMain(p));

            Assert.IsTrue(started);
        }
    }
}

