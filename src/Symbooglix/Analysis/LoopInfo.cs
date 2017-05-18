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
using Microsoft.Boogie;
using System.Diagnostics;
using System.Numerics;
using System.Collections.Generic;
using System.Linq;
namespace Symbooglix
{
    public class LoopInfo
    {
        // TODO: Figure out how to represent nested loop references
        public Block Header { get; private set; }
        public HashSet<Block> LoopBlocks { get; private set; }
        public HashSet<Block> EscapingBlocks { get; private set; }
        public LoopInfo(Block header, HashSet<Block> loopBlocks, HashSet<Block> escapingBlocks)
        {
            Header = header;
            LoopBlocks = loopBlocks;
            EscapingBlocks = escapingBlocks;
        }
    }

    public class ProgramLoopInfo
    {
        protected Dictionary<Block, LoopInfo> HeaderToLoopInfo;
        public Program Prog { get; private set; }
        public ProgramLoopInfo(Program p)
        {
            HeaderToLoopInfo = new Dictionary<Block, LoopInfo>();
            Prog = p;
            InitLoopInfo();
        }
        public LoopInfo GetLoopInfoForHeader(Block header)
        {
            try
            {
                return HeaderToLoopInfo[header];
            }
            catch (KeyNotFoundException)
            {
                return null;
            }
        }
        private void InitLoopInfo()
        {
            // Compute the basic blocks that escape loops
            foreach (var impl in Prog.Implementations) {
                var CFG = Program.GraphFromImpl(impl);
                CFG.ComputeLoops();
                foreach (var Header in CFG.Headers) {
                    var allBlocksInThisLoop = new HashSet<Block>();
                    foreach (var BackEdge in CFG.BackEdgeNodes(Header))
                    {
                        foreach (var block in CFG.NaturalLoops(Header, BackEdge))
                        {
                            allBlocksInThisLoop.Add(block);
                        }
                    }

                    var escapingBlocks = new HashSet<Block>();
                    foreach (var b in allBlocksInThisLoop) {
                        var gotoCmd = b.TransferCmd as GotoCmd;
                        if (gotoCmd != null) {
                            foreach (var gotoTargetBlock in gotoCmd.labelTargets)
                            {
                                if (!(allBlocksInThisLoop.Contains(gotoTargetBlock)))
                                {
                                    // Blocks reachable from inside the loop that
                                    // are not part of the loop are escaping blocks
                                    escapingBlocks.Add(gotoTargetBlock);
                                }
                            }
                        }
                    }
                    // Create LoopInfo
                    var loopInfo = new LoopInfo(Header, allBlocksInThisLoop, escapingBlocks);
                    HeaderToLoopInfo.Add(Header, loopInfo);
                }
            }
        }
    }


    public class ExecutionStateSingleLoopInfo
    {
        // The stackframe that the loop is being executed in.
        public StackFrame Stack { get; private set; }
        public LoopInfo LInfo { get; private set; }
        public BigInteger Counter { get; private set; }
        public void IncrementCounter()
        {
            ++Counter;
        }
        public ExecutionStateSingleLoopInfo(StackFrame stack, LoopInfo li)
        {
            Stack = stack;
            LInfo = li;
            Counter = 0;
        }

        public ExecutionStateSingleLoopInfo Clone(StackFrame sf)
        {
            var other = (ExecutionStateSingleLoopInfo) this.MemberwiseClone();
            other.Stack = sf;
            // No need to copy `Counter` because it is a value type.
            return other;
        }
    }


    public class ExecutionStateNestedLoopInfo
    {
        public Stack<ExecutionStateSingleLoopInfo> NestedLoops;
        public ExecutionState State { get; private set; }
        public ExecutionStateNestedLoopInfo(ExecutionState state)
        {
            NestedLoops = new Stack<ExecutionStateSingleLoopInfo>();
            State = state;
        }

        protected StackFrame GetCorrespondingStackFrame(ExecutionState newState, StackFrame oldStateStackFrame)
        {
            int index = 0;
            bool found = false;
            if (newState.Mem.Stack.Count != State.Mem.Stack.Count)
                throw new ArgumentException("New state does not have same size stackframe as old state");
            foreach (var sf in State.Mem.Stack)
            {
                if (object.ReferenceEquals(oldStateStackFrame, sf))
                {
                    found = true;
                    break;
                }
                ++index;
            }
            if (!found)
                throw new ArgumentException("Could not find StackFrame in state");
            return newState.Mem.Stack[index];
        }

        public ExecutionStateNestedLoopInfo Clone(ExecutionState newState)
        {
            var other = (ExecutionStateNestedLoopInfo) this.MemberwiseClone();
            other.State = newState;
            other.NestedLoops = new Stack<ExecutionStateSingleLoopInfo>(NestedLoops.Count);

            // Traverse in reverse order (i.e. start at bottom of the stack)
            // so we can push elements on to the new stack in the right order
            foreach (var sli in NestedLoops.Reverse())
            {
                StackFrame stackFrameInNewState = GetCorrespondingStackFrame(newState, sli.Stack);
                ExecutionStateSingleLoopInfo newSli = sli.Clone(stackFrameInNewState);
                other.NestedLoops.Push(newSli);
            }
            Debug.Assert(other.NestedLoops.Count == NestedLoops.Count);
            return other;
        }
    }
}
