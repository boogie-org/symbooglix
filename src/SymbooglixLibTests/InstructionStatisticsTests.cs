//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using NUnit.Framework;
using System;
using Symbooglix;
using System.Linq;
using Microsoft.Boogie;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class InstructionStatisticsTests : SymbooglixTest
    {
        [Test()]
        public void LookAheadGoto()
        {
            p = LoadProgramFrom("programs/InstructionStatistics.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            e.Run(GetMain(p));
            DoTest(4, 1, 3, 3, 1);
        }

        private void DoTest(int expectedLoopHeadTotalJumps,
                            int expectedLoopHeadJumpsToLoopDone,
                            int expectedLoopHeadJumpsToLoopBody,
                            int expectedLoopBodyAssumeCoverage,
                            int expectedLoopDoneAssumeCoverage)
        {
            // Check we executed foo three times
            var foo = p.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Name == "foo").First();
            foreach (var cmd in foo.Blocks[0].Cmds)
                Assert.AreEqual(3, cmd.GetInstructionStatistics().Covered);

            Assert.AreEqual(3, (foo.Blocks[0].TransferCmd as ReturnCmd).GetInstructionStatistics().Covered);

            // Check foo's requires and ensures were covered
            foreach (var requires in foo.Proc.Requires)
                Assert.AreEqual(3, requires.GetInstructionStatistics().Covered);

            foreach (var ensures in foo.Proc.Ensures)
                Assert.AreEqual(3, ensures.GetInstructionStatistics().Covered);

            // Check the axioms were covered
            var axioms = p.TopLevelDeclarations.OfType<Axiom>();
            Assert.AreEqual(1, axioms.Count());
            foreach (var axiom in axioms)
                Assert.AreEqual(1, axiom.GetInstructionStatistics().Covered);

            // Check execution of main
            var main = p.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Name == "main").First();

            var entryBlock = main.Blocks[0];
            Assert.AreEqual("anon0", entryBlock.Label);
            CheckBlockCount(entryBlock, 1);

            var loopHead = main.Blocks[1];
            Assert.AreEqual("anon2_LoopHead", loopHead.Label);
            CheckBlockCount(loopHead, 4);

            var loopBody = main.Blocks[2];
            Assert.AreEqual("anon2_LoopBody", loopBody.Label);

            // The assume might get visited one extra time depending on the goto implementation being used.
            CheckBlockStartingWithAssumeCount(loopBody, expectedLoopBodyAssumeCoverage, 3);

            var loopDone = main.Blocks[3];
            Assert.AreEqual("anon2_LoopDone", loopDone.Label);
            CheckBlockStartingWithAssumeCount(loopDone, expectedLoopDoneAssumeCoverage, 1);

            // Check the goto of entry block
            var gotoStats = entryBlock.TransferCmd.GetInstructionStatistics() as GotoInstructionStatistics;
            Assert.AreEqual(1, gotoStats.TotalJumps);
            Assert.AreEqual(1, gotoStats.GetJumpsTo(loopHead));

            // Check the goto of loopHead
            var loopHeadGotoStats = loopHead.TransferCmd.GetInstructionStatistics() as GotoInstructionStatistics;
            Assert.AreEqual(expectedLoopHeadTotalJumps, loopHeadGotoStats.TotalJumps);
            Assert.AreEqual(expectedLoopHeadJumpsToLoopDone, loopHeadGotoStats.GetJumpsTo(loopDone));
            Assert.AreEqual(expectedLoopHeadJumpsToLoopBody, loopHeadGotoStats.GetJumpsTo(loopBody));

            // Check the goto of loopBody
            var loopBodyGotoStats = loopBody.TransferCmd.GetInstructionStatistics() as GotoInstructionStatistics;
            Assert.AreEqual(3, loopBodyGotoStats.TotalJumps);
            Assert.AreEqual(3, loopBodyGotoStats.GetJumpsTo(loopHead));

            // Check termination occurred at the ReturnCmd
            Assert.AreEqual(1, loopDone.TransferCmd.GetInstructionStatistics().Terminations);
        }

        [Test()]
        public void NaiveGoto()
        {
            p = LoadProgramFrom("programs/InstructionStatistics.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = false;

            e.Run(GetMain(p));
            DoTest(8, 4, 4, 4, 4);

            // Check the terminations as the AssumeCmds
            var main = p.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Name == "main").First();
            var LoopBodyAssume = main.Blocks[2].Cmds[0] as AssumeCmd;
            var LoopDoneAssume = main.Blocks[3].Cmds[0] as AssumeCmd;
            Assert.AreEqual(1, LoopBodyAssume.GetInstructionStatistics().Terminations);
            Assert.AreEqual(3, LoopDoneAssume.GetInstructionStatistics().Terminations);
        }

        private void CheckBlockCount(Block bb, int count)
        {
            foreach (var cmd in bb.Cmds)
                Assert.AreEqual(count, cmd.GetInstructionStatistics().Covered, "Cmd: " + cmd.ToString() + " was not executed the expected number of times");

            Assert.AreEqual(count, bb.TransferCmd.GetInstructionStatistics().Covered);
        }

        private void CheckBlockStartingWithAssumeCount(Block bb, int assumeCount, int restOfCodeCount)
        {
            Assert.AreEqual(assumeCount, bb.Cmds[0].GetInstructionStatistics().Covered);
            for (int index = 1; index < bb.Cmds.Count; ++index)
                Assert.AreEqual(restOfCodeCount, bb.Cmds[index].GetInstructionStatistics().Covered);
            Assert.AreEqual(restOfCodeCount, bb.TransferCmd.GetInstructionStatistics().Covered);
        }

        [Test()]
        public void MultipleForksLookAhead()
        {
            p = LoadProgramFrom("programs/MultipleForks.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var tc = new TerminationCounter();
            tc.Connect(e);
            e.Run(GetMain(p));

            Assert.AreEqual(5, tc.Sucesses);

            // LoopHead goto
            var gotoCmd = GetMain(p).Blocks[2].TransferCmd;
            Assert.AreEqual(4, gotoCmd.GetInstructionStatistics().Forks);
        }

        [Test()]
        public void MultipleForksNaiveGoto()
        {
            p = LoadProgramFrom("programs/MultipleForks.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = false;

            var tc = new TerminationCounter();
            tc.Connect(e);
            e.Run(GetMain(p));

            Assert.AreEqual(5, tc.Sucesses);

            // LoopHead goto
            var gotoCmd = GetMain(p).Blocks[2].TransferCmd;
            Assert.AreEqual(5, gotoCmd.GetInstructionStatistics().Forks);
        }
    }
}

