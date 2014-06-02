using System;

namespace symbooglix
{
    public interface ITerminationHandler
    {
        void handleSuccess(ExecutionState s);
        void handleFailingAssert(ExecutionState s);
        void handleFailingEnsures(ExecutionState s);
        void handleUnsatisfiableAssume(ExecutionState s);
    }
}

