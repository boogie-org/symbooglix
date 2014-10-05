using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.Diagnostics;

namespace Symbooglix
{
    public class InstructionStatistics
    {
        public int Covered
        {
            get;
            private set;
        }

        // TODO fork count

        public InstructionStatistics()
        {
            this.Covered = 0;
        }

        public void IncrementCovered()
        {
            ++Covered;
        }
    }

    public class GotoInstructionStatistics : InstructionStatistics
    {
        // Maps targets visitable from the goto to visit cound
        private Dictionary<Block,int> TargetsVisited;

        public GotoInstructionStatistics(Microsoft.Boogie.GotoCmd gotoCmd)
        {
            TargetsVisited = new Dictionary<Block, int>();

            foreach (var target in gotoCmd.labelTargets)
                TargetsVisited[target] = 0;
        }

        public void IncrementJumpTo(Block block)
        {
            Debug.Assert(TargetsVisited.ContainsKey(block), "Target is not part of goto");
            int currentValue = TargetsVisited[block];
            ++currentValue;
            TargetsVisited[block] = currentValue;
        }

        public int TotalJumps
        {
            get
            {
                int jumps = 0;
                foreach (var count in TargetsVisited.Values)
                    jumps += count;

                return jumps;
            }
        }

        public int GetJumpsTo(Block block)
        {
            Debug.Assert(TargetsVisited.ContainsKey(block), "Target is not part of goto");
            return TargetsVisited[block];
        }
    }
}

