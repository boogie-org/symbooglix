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

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class ArithmeticCoercion : SymbooglixTest
    {
        public void Init(string program)
        {
            this.p = LoadProgramFrom(program);

            var solver = GetSolver();
            // No constant folding needed so that the ArithmeticCoercion reaches the solver
            this.e = GetExecutor(this.p, new DFSStateScheduler(), solver, /*useConstantFolding=*/ false);
        }

        [Test()]
        public void RealToInt()
        {
            var counter = new TerminationCounter();
            Init("programs/RealToInt.bpl");
            counter.Connect(e);
            e.Run(GetMain(this.p));
            checkCounter(counter);
        }

        [Test()]
        public void IntToReal()
        {
            var counter = new TerminationCounter();
            Init("programs/IntToReal.bpl");
            counter.Connect(e);
            e.Run(GetMain(this.p));
            checkCounter(counter);
        }

        void checkCounter(TerminationCounter counter)
        {
            Assert.AreEqual(counter.Sucesses, 1);
            Assert.AreEqual(counter.FailingAsserts, 0);
        }
    }
}

