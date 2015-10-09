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
using Microsoft.Boogie;

namespace Symbooglix
{
    /// <summary>
    /// Alternative BFS state scheduler.
    /// This implementation looks for GotoCmds and halts states there until
    /// all states it has are about to execute a GotoCmd. Then it executes those
    /// states and then the process starts again.
    /// </summary>
    public class AlternativeBFSStateScheduler : IStateScheduler
    {
        private List<ExecutionState> NotAboutToDoGoto;
        private List<ExecutionState> AboutToDoGoto;

        public AlternativeBFSStateScheduler()
        {
            NotAboutToDoGoto = new List<ExecutionState>();
            AboutToDoGoto = new List<ExecutionState>();
        }

        private int GotoIntCounter = 0;

        public ExecutionState GetNextState()
        {
            while (NotAboutToDoGoto.Count > 0)
            {
                var state = NotAboutToDoGoto[0];
                var nextCmd = GetNextCmd(state);

                if (nextCmd is Microsoft.Boogie.GotoCmd)
                {
                    // Move state to the other list
                    AboutToDoGoto.Add(state);
                    NotAboutToDoGoto.RemoveAt(0);
                }
                else
                    return state;
            }

            Debug.Assert(NotAboutToDoGoto.Count == 0);

            if (AboutToDoGoto.Count == 0)
            {
                // There are no states left to explore
                return null;
            }

            // Try to ensure we execute the Gotos
            for (int index = GotoIntCounter; index < AboutToDoGoto.Count; ++index)
            {
                var state = AboutToDoGoto[index];
                var nextCmd = GetNextCmd(state);

                GotoIntCounter = index; // Next call we'll start further in the list

                if (nextCmd is GotoCmd)
                    return state;
            }

            GotoIntCounter = 0;

            // Need to swap list as states are available in it
            SwapLists();
            return GetNextState();

        }

        private Absy GetNextCmd(ExecutionState state)
        {
            var nextCmd = state.GetCurrentStackFrame().CurrentInstruction.Clone();
            nextCmd.MoveNext();
            return nextCmd.Current;
        }

        private void SwapLists()
        {
            var temp = AboutToDoGoto;
            AboutToDoGoto = NotAboutToDoGoto;
            NotAboutToDoGoto = temp;
        }

        public void AddState(ExecutionState toAdd)
        {
            Debug.Assert(!NotAboutToDoGoto.Contains(toAdd), "Cannot add state already held by scheduler");
            Debug.Assert(!AboutToDoGoto.Contains(toAdd), "Cannot add state already held by scheduler");
            AboutToDoGoto.Add(toAdd);
        }

        public void RemoveState(ExecutionState toRemove)
        {
            bool success = NotAboutToDoGoto.Remove(toRemove);

            if (!success)
                AboutToDoGoto.Remove(toRemove);
        }

        public void RemoveAll()
        {
            NotAboutToDoGoto.Clear();
            AboutToDoGoto.Clear();
        }

        public int GetNumberOfStates()
        {
            return NotAboutToDoGoto.Count + AboutToDoGoto.Count;
        }

        public void ReceiveExecutor(Executor executor)
        {
            // Not needed
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            TW.WriteLine("name : \"{0}\"", this.GetType().ToString());
        }
    }
}

