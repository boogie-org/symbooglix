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
    public class ExecutorNonTerminatedStateRemovedEvent : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = LoadProgramFrom("programs/InfiniteLoop.bpl");
            // We need to use constant folding otherwise this test can non deterministically fail
            // because without constant folding the solver will be asked to evaluate the exit block
            // "assume !true" which can non-deterministically return UNKNOWN because of the timeout.
            // With constant folding the solver is never used and so we can never get a speculative
            // execution state that leaves the loop
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver(), /*useConstantFolding=*/true);

            var tc = new TerminationCounter();
            int counter = 0;
            e.NonTerminatedStateRemoved += delegate(object sender, Executor.ExecutionStateEventArgs eventArgs)
            {
                Assert.IsFalse(eventArgs.State.Finished());
                Assert.IsNull(eventArgs.State.TerminationType);
                Console.WriteLine("state {0}", eventArgs.State.Id);
                using (var ITW = new System.CodeDom.Compiler.IndentedTextWriter(Console.Out))
                {
                    eventArgs.State.WriteAsYAML(ITW);
                }

                // FIXME: Id should **NOT* be a static counter because it is shared across all Executors which is bad
                //Assert.AreEqual(0, eventArgs.State.Id);

                ++counter;
            };

            tc.Connect(e);

            // Run with timeout
            e.Run(GetMain(p),1);
            Assert.AreEqual(1, counter);
            Assert.AreEqual(0, tc.NumberOfTerminatedStates);
        }
    }
}

