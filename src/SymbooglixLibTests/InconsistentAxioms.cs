using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class InconsistentAxioms : SymbooglixTest
    {
        private void Init()
        {
            p = loadProgram("programs/InconsistentAxioms.bpl");
            this.e = getExecutor(p, new DFSStateScheduler(), GetSolver());
        }

        [Test()]
        public void Notified()
        {
            Init();
            var TC = new TerminationCounter();
            TC.Connect(e);

            try
            {
                e.Run(getMain(p));
            }
            catch
            {
                // Don't do anything
            }

            Assert.AreEqual(1, TC.UnsatisfiableAxioms);
            Assert.AreEqual(1, TC.NumberOfFailures);
        }

        [ExpectedException(typeof(Symbooglix.ExecuteTerminatedStateException))]
        public void ExceptionThrown()
        {
            Init();
            e.Run(getMain(p));

        }
    }


}

