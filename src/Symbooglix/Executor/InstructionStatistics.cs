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

namespace Symbooglix
{
    public class InstructionStatistics
    {
        public int Covered
        {
            get;
            private set;
        }

        public int Terminations
        {
            get;
            private set;
        }

        public int Forks
        {
            get;
            private set;
        }

        public InstructionStatistics()
        {
            this.Covered = 0;
            this.Terminations = 0;
            this.Forks = 0;
        }

        public void IncrementCovered()
        {
            ++Covered;
        }

        public void IncrementTerminations()
        {
            ++Terminations;
        }

        public void IncrementForks()
        {
            ++Forks;
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


        /// <summary>
        /// Creates a duplicate of the GotoInstructionStatistics but with Blocks remapped.
        /// This is useful for working duplicated programs which may point to the Blocks
        //  of the old program
        /// </summary>
        /// <returns>The modified copy</returns>
        /// <param name="substitution">Substitution.</param>
        public GotoInstructionStatistics BlockSubstitution(Dictionary<Block,Block> substitution)
        {
            var newTargetsVisited = new Dictionary<Block,int>();

            foreach (var pair in TargetsVisited)
            {
                newTargetsVisited.Add(substitution[pair.Key], TargetsVisited[pair.Key]);
            }

            // We need to do a clone because we want to copy over all the other statistics by value
            var other = (GotoInstructionStatistics) this.MemberwiseClone();
            other.TargetsVisited = newTargetsVisited;
            return other;
        }
    }
}

