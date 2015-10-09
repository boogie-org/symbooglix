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
using Symbooglix.Solver;
using System;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class OnlyOneSolverCall : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            SolverStats beforeAssert;
            SolverStats afterAssert;
            p = LoadProgramFrom("programs/OnlyOneSolverCall.bpl");
            ISolver Solver = GetSolver();
            e = GetExecutor(p, new DFSStateScheduler(), Solver);

            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name == "before_assert")
                {
                    beforeAssert = Solver.Statistics;
                }
                else if (data.Name == "after_assert")
                {
                    afterAssert = Solver.Statistics;
                }
                else
                    Assert.Fail("Unexpected breakpoint :" + data.Name);
            };


            e.Run(GetMain(p));
            Assert.IsNotNull(beforeAssert);
            Assert.IsNotNull(afterAssert);

            Assert.AreEqual(1, beforeAssert.TotalQueries);
            Assert.AreEqual(2, afterAssert.TotalQueries);

        }
    }
}

