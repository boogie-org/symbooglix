using NUnit.Framework;
using Symbooglix;
using System;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class MapExtensionality : SymbooglixTest, ITerminationHandler
    {
        [Test()]
        public void TestCase()
        {
            p= loadProgram("programs/MapExtensionality.bpl");
            var executor = getExecutor(p, new DFSStateScheduler(), GetSolver());
            executor.RegisterTerminationHandler(this);
            executor.Run(getMain(p));

        }

        public void handleSuccess(ExecutionState s)
        {
            // Don't need to so anything
        }

        public void handleFailingAssert(ExecutionState s)
        {
            Assert.Fail("Boogie assertion failed");
        }

        public void handleUnsatisfiableRequires(ExecutionState s, Microsoft.Boogie.Requires requiresStatement)
        {
            throw new NotImplementedException();
        }

        public void handleFailingEnsures(ExecutionState s, Microsoft.Boogie.Ensures ensuresStatement)
        {
            throw new NotImplementedException();
        }

        public void handleUnsatisfiableAssume(ExecutionState s)
        {
            Assert.Fail("Boogie assume failed");
        }
    }
}

