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
            this.p = loadProgram(program);

            var solver = GetSolver();
            this.e = getExecutor(this.p, new DFSStateScheduler(), solver);

            // Needed so that the ArithmeticCoercion reaches the solver
            this.e.UseConstantFolding = false;
        }

        [Test()]
        public void RealToInt()
        {
            var counter = new TerminationCounter();
            Init("programs/RealToInt.bpl");
            e.RegisterTerminationHandler(counter);
            e.Run(getMain(this.p));
            checkCounter(counter);
        }

        [Test()]
        public void IntToReal()
        {
            var counter = new TerminationCounter();
            Init("programs/IntToReal.bpl");
            e.RegisterTerminationHandler(counter);
            e.Run(getMain(this.p));
            checkCounter(counter);
        }

        void checkCounter(TerminationCounter counter)
        {
            Assert.AreEqual(counter.Sucesses, 1);
            Assert.AreEqual(counter.FailingAsserts, 0);
        }
    }
}

