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
    public class Ensures : SymbooglixTest
    {
        [Test()]
        public void concreteEnsuresFeasible()
        {
            p = LoadProgramFrom(@"
                var g:bv8;
                procedure main()
                requires g == 0bv8;
                modifies g;
                ensures g == 2bv8;
                {
                    g := 2bv8;
                }
                ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver(), /*useConstantFolding*/ false);
            var tc = new TerminationCounter();
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(1, tc.Sucesses);
            Assert.AreEqual(0, tc.NumberOfFailures);
        }

        [Test()]
        public void concreteEnsuresInfeasible()
        {
            p = LoadProgramFrom(@"
                var g:bv8;
                procedure main()
                requires g == 0bv8;
                modifies g;
                ensures g == 2bv8;
                {
                    g := 1bv8;
                }
                ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver(), /*useConstantFolding*/ false);
            var tc = new TerminationCounter();
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(0, tc.Sucesses);
            Assert.AreEqual(1, tc.NumberOfFailures);
            Assert.AreEqual(1, tc.FailingEnsures);
        }

        [Test()]
        public void symbolicEnsures()
        {
            p = LoadProgramFrom(@"
                var g:bv8;
                procedure main()
                requires g == 0bv8;
                modifies g;
                ensures g == 2bv8;
                {
                    havoc g;
                }
                ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver(), /*useConstantFolding*/ false);
            var tc = new TerminationCounter();
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(1, tc.Sucesses);
            Assert.AreEqual(1, tc.NumberOfFailures);
            Assert.AreEqual(1, tc.FailingEnsures);
        }
    }
}

