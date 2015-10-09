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
using Microsoft.Boogie;
using System.Diagnostics;
using System.Linq;

namespace Symbooglix
{
    public class LoopEscapingScheduler : IStateScheduler
    {
        IStateScheduler UnderlyingScheduler;
        HashSet<Block> EscapingBlocks = null;
        Stack<ExecutionState> LoopEscapingStates;
        public LoopEscapingScheduler(IStateScheduler underlyingScheduler)
        {
            this.UnderlyingScheduler = underlyingScheduler;
            this.LoopEscapingStates = new Stack<ExecutionState>();
            // Deliberately do not initialise EscapingBlocks here
        }

        public ExecutionState GetNextState()
        {
            Debug.Assert(EscapingBlocks != null, "Escaping blocks not set");

            if (LoopEscapingStates.Count > 0)
                return LoopEscapingStates.Peek();

            return UnderlyingScheduler.GetNextState();
        }

        public void AddState(ExecutionState toAdd)
        {
            Debug.Assert(EscapingBlocks != null, "Escaping blocks not set");
            var block = toAdd.GetCurrentBlock();
            if (block != null && EscapingBlocks.Contains(block))
            {
                // This state appears to be in a block that leaves a loop.
                LoopEscapingStates.Push(toAdd);
            }
            else
                UnderlyingScheduler.AddState(toAdd);
        }

        public void RemoveState(ExecutionState toRemove)
        {
            Debug.Assert(EscapingBlocks != null, "Escaping blocks not set");

            // Fast path
            if (LoopEscapingStates.Count > 0 && LoopEscapingStates.Peek() == toRemove)
            {
                LoopEscapingStates.Pop();
                return;
            }

            // FIXME: This might be slow
            if (LoopEscapingStates.Contains(toRemove))
            {
                int initialStates = LoopEscapingStates.Count;

                // The item we want to remove is not on the top of the stack
                // pop items until we find it, remove it and then pop the items back on
                Stack<ExecutionState> statesToAddBack = new Stack<ExecutionState>();
                while (LoopEscapingStates.Peek() != toRemove)
                {
                    statesToAddBack.Push(LoopEscapingStates.Pop());
                }

                // Pop the state to remove
                var state = LoopEscapingStates.Pop();
                Debug.Assert(state == toRemove, "We removed the wrong state!");

                // but the other states back
                while (statesToAddBack.Count > 0)
                {
                    LoopEscapingStates.Push(statesToAddBack.Pop());
                }

                Debug.Assert(LoopEscapingStates.Count == (initialStates - 1), "The number of states removed was incorrect");
            }
            else
                UnderlyingScheduler.RemoveState(toRemove);
        }

        public void RemoveAll()
        {
            Debug.Assert(EscapingBlocks != null, "Escaping blocks not set");
            LoopEscapingStates.Clear();
            UnderlyingScheduler.RemoveAll();
        }

        public int GetNumberOfStates()
        {
            Debug.Assert(EscapingBlocks != null, "Escaping blocks not set");
            return LoopEscapingStates.Count + UnderlyingScheduler.GetNumberOfStates();
        }

        public void ReceiveExecutor(Executor executor)
        {
            EscapingBlocks = new HashSet<Block>();

            // Compute the basic blocks that escape loops
            foreach(var impl in executor.TheProgram.Implementations)
            {
                var CFG = Program.GraphFromImpl(impl);
                CFG.ComputeLoops();
                foreach (var Header in CFG.Headers)
                {
                    var allBlocksInThisLoop = new HashSet<Block>();
                    foreach (var BackEdge in CFG.BackEdgeNodes(Header))
                    {
                        foreach (var block in CFG.NaturalLoops(Header, BackEdge))
                        {
                            allBlocksInThisLoop.Add(block);
                        }
                    }

                    foreach (var b in allBlocksInThisLoop)
                    {
                        var gotoCmd = b.TransferCmd as GotoCmd;
                        if (gotoCmd != null)
                        {
                            foreach (var gotoTargetBlock in gotoCmd.labelTargets)
                            {
                                if (!(allBlocksInThisLoop.Contains(gotoTargetBlock)))
                                {
                                    // Blocks reachable from inside the loop that
                                    // are not part of the loop are escaping blocks
                                    EscapingBlocks.Add(gotoTargetBlock);
                                }
                            }
                        }
                    }
                }
            }

        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            TW.WriteLine("name : \"{0}\"", this.GetType().ToString());
            TW.WriteLine("underlying_scheduler:");
            TW.Indent += 1;
            UnderlyingScheduler.WriteAsYAML(TW);
            TW.Indent -= 1;
        }
    }
}

