using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public interface IStateScheduler : Util.IDumpable
    {
        ExecutionState GetNextState();
        void AddState(ExecutionState toAdd);
        void RemoveState(ExecutionState toRemove);
        void RemoveAll();
        int GetNumberOfStates();
        void ReceiveExecutor(Executor executor);
    }
}

