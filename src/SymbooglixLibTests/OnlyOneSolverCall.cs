using Microsoft.Boogie;
using NUnit.Framework;
using Symbooglix;
using Symbooglix.Solver;
using System;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class OnlyOneSolverCall : SymbooglixTest, IBreakPointHandler
    {
        ISolver Solver;
        SolverStats beforeAssert = null;
        SolverStats afterAssert = null;
        [Test()]
        public void TestCase()
        {
            p = loadProgram("programs/OnlyOneSolverCall.bpl");
            this.Solver = GetSolver();
            e = getExecutor(p, new DFSStateScheduler(), this.Solver);
            e.RegisterBreakPointHandler(this);
            e.Run(getMain(p));
            Assert.IsNotNull(beforeAssert);
            Assert.IsNotNull(afterAssert);

            Assert.AreEqual(1, beforeAssert.TotalQueries);
            Assert.AreEqual(2, afterAssert.TotalQueries);

        }

        public Executor.HandlerAction handleBreakPoint(string name, Executor e)
        {
            // Need to clone the SolverStats object so we have
            // an instance of SolverStats that won't change.
            if (name == "before_assert")
            {
                beforeAssert = Solver.Statistics.DeepClone();
            }
            else if (name == "after_assert")
            {
                afterAssert = Solver.Statistics.DeepClone();
            }
            else
                Assert.Fail("Unexpected breakpoint :" + name);

            return Executor.HandlerAction.CONTINUE;
        }
    }
}

