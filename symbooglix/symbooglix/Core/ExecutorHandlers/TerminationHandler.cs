using System;

namespace symbooglix
{
    public interface ITerminationHandler
    {
        void handleSuccess(ExecutionState s);
        void handleAssertFail(ExecutionState s);
        void handleEnsuresFail(ExecutionState s);
    }
}

