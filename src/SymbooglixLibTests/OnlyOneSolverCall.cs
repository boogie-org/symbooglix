﻿using Microsoft.Boogie;
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
            SolverStats beforeAssert = null;
            SolverStats afterAssert = null;
            p = loadProgram("programs/OnlyOneSolverCall.bpl");
            ISolver Solver = GetSolver();
            e = getExecutor(p, new DFSStateScheduler(), Solver);

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


            e.Run(getMain(p));
            Assert.IsNotNull(beforeAssert);
            Assert.IsNotNull(afterAssert);

            Assert.AreEqual(1, beforeAssert.TotalQueries);
            Assert.AreEqual(2, afterAssert.TotalQueries);

        }
    }
}
