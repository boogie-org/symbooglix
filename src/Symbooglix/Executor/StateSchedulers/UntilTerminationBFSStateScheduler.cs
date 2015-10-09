//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    /// <summary>
    /// This state scheduler visits states in BFS order but lets
    /// an ExecutionState terminate before it will consider the next
    /// state to visit.
    /// </summary>
    public class UntilTerminationBFSStateScheduler : IStateScheduler
    {
        private List<ExecutionState> States;
        public UntilTerminationBFSStateScheduler() 
        { 
            States = new List<ExecutionState>();
        }

        public ExecutionState GetNextState() 
        { 
            if (States.Count == 0)
                return null;

            return States[0];
        }

        public int GetNumberOfStates() { return States.Count;}

        public void AddState (ExecutionState toAdd)
        {
            States.Add(toAdd);
        }

        public void RemoveState(ExecutionState toRemove)
        {
            Debug.Assert(States.Contains(toRemove), "Cannot remove state not stored in the state scheduler");
            States.Remove(toRemove);
        }

        public void RemoveAll()
        {
            States.Clear();
        }

        public void ReceiveExecutor(Executor executor)
        {
            // Not Needed
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            TW.WriteLine("name : \"{0}\"", this.GetType().ToString());
        }
    }
}

