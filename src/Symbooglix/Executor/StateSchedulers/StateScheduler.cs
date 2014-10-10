using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public interface IStateScheduler
    {
        ExecutionState GetNextState();
        void UpdateStates(List<ExecutionState> toAdd, List<ExecutionState> toRemove);
        void AddState(ExecutionState toAdd);
        void RemoveState(ExecutionState toRemove);
        void RemoveAll(Predicate<ExecutionState> p);
        int GetNumberOfStates();
    }
}

