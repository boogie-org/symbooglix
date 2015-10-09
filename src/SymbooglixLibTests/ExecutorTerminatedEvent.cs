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
using Symbooglix.Solver;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class ExecutorTerminatedEvent : SymbooglixTest
    {
        public void InitAndRun(string program)
        {
            bool hit = false;
            p = LoadProgramFrom(program);
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            e.ExecutorTerminated += delegate(object sender, Executor.ExecutorTerminatedArgs executorTerminatedArgs)
            {
                hit = true;
            };
            try
            {
                e.Run(GetMain(p));
            }
            catch (InitialStateTerminated)
            {
                // Ignore for now
            }

            Assert.IsTrue(hit);
        }

        [Test()]
        public void FailingAssert()
        {
            InitAndRun("programs/assert_false.bpl");
        }

        [Test()]
        public void TerminateWithoutError()
        {
            InitAndRun("programs/assert_true.bpl");
        }


        [Test()]
        public void UnsatAssume()
        {
            InitAndRun("programs/assume_false.bpl");
        }


        [Test()]
        public void UnsatEntryRequires()
        {
            InitAndRun("programs/UnsatisfiableEntryRequires.bpl");
        }


        [Test()]
        public void FailingRequires()
        {
            InitAndRun("programs/FailingRequires.bpl");

        }

        [Test()]
        public void FailingEnsures()
        {
            InitAndRun("programs/FailingEnsures.bpl");
        }

        [Test()]
        public void UnsatEnsures()
        {
            InitAndRun("programs/UnsatisfiableEnsures.bpl");
        }

        [Test()]
        public void UnsatAxiom()
        {
            InitAndRun("programs/InconsistentAxioms.bpl");
        }

        [Test()]
        public void DisallowedSpeculativeExecutionPath()
        {
            p = LoadProgramFrom("programs/TwoPaths.bpl");

            // By using a dummy solver which always returns "UNKNOWN" every path should
            // be consider to be speculative
            e = GetExecutor(p, new DFSStateScheduler(), new SimpleSolver( new DummySolver(Result.UNKNOWN)));

            bool hit = false;
            e.ExecutorTerminated += delegate(object sender, Executor.ExecutorTerminatedArgs executorEventArgs)
            {
                hit = true;
            };
            e.Run(GetMain(p));
            Assert.IsTrue(hit);
        }
    }
}

