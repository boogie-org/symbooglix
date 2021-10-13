//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2017 Daniel Liew
//
// This file is licensed under the MIT license.
// See LICENSE.txt for details.
//------------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public interface IStateScheduler : Util.IYAMLWriter
    {
        ExecutionState GetNextState();
        void AddState(ExecutionState toAdd);
        void RemoveState(ExecutionState toRemove);
        void RemoveAll();
        int GetNumberOfStates();
        void ReceiveExecutor(Executor executor);
    }
}

