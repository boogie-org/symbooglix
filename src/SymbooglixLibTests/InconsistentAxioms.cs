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

        [Test(),ExpectedException(typeof(Symbooglix.ExecuteTerminatedStateException))]
        public void ExceptionThrown()
        {
            Init();
            e.Run(getMain(p));

        }
    }


}

