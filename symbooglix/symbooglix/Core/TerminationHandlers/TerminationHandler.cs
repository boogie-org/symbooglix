using System;

namespace symbooglix
{
    public interface ITerminationHandler
    {
        void handleSuccess(ExecutionState s);
        void handleFailingAssert(ExecutionState s);
        void handleUnsatisfiableRequires(ExecutionState s, Microsoft.Boogie.Requires requiresStatement);
        void handleFailingEnsures(ExecutionState s, Microsoft.Boogie.Ensures ensuresStatement);
        void handleUnsatisfiableAssume(ExecutionState s);
    }
}

