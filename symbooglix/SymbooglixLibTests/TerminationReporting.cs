using NUnit.Framework;
using System;
using symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class TerminationReporting : SymbooglixTest, ITerminationHandler
    {
        private int failingAssertCount = 0;
        private int successCount = 0;
        private int failingEnsuresCount = 0;
        private int UnsatisfiableAssumeCount = 0;
        private int UnsatisfiableRequiresCount = 0;

        public void ResetCounters()
        {
            failingAssertCount = 0;
            successCount = 0;
            failingEnsuresCount = 0;
            UnsatisfiableAssumeCount = 0;
            UnsatisfiableRequiresCount = 0;
        }

        [Test()]
        public void FailingAssert()
        {
            ResetCounters();
            p = loadProgram("programs/assert_false.bpl");
            e = getExecutor(p);
            e.registerTerminationHandler(this);
            e.run(getMain(p));
            Assert.AreEqual(failingAssertCount, 1);
        }

        [Test()]
        public void TerminateWithoutError()
        {
            ResetCounters();
            p = loadProgram("programs/assert_true.bpl");
            e = getExecutor(p);
            e.registerTerminationHandler(this);
            e.run(getMain(p));
            Assert.AreEqual(failingAssertCount, 0);
            Assert.AreEqual(successCount, 1);
        }

        [Test()]
        public void UnsatAssume()
        {
            ResetCounters();
            p = loadProgram("programs/assume_false.bpl");
            e = getExecutor(p);
            e.registerTerminationHandler(this);
            e.run(getMain(p));
            Assert.AreEqual(UnsatisfiableAssumeCount, 1);
        }

        public void handleSuccess(ExecutionState s)
        {
            ++successCount;
        }

        public void handleFailingAssert(ExecutionState s)
        {
            ++failingAssertCount;
        }

        public void handleFailingEnsures(ExecutionState s)
        {
            ++failingEnsuresCount;
        }

        public void handleUnsatisfiableAssume(ExecutionState s)
        {
            ++UnsatisfiableAssumeCount;
        }

        public void handleUnsatisfiableRequires (ExecutionState s, Microsoft.Boogie.Requires requiresStatement)
        {
            ++UnsatisfiableRequiresCount;
        }
    }
}

