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
            p = loadProgram("programs/InstructionStatistics.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            e.Run(getMain(p));

            // Check we executed foo three times
            var foo = p.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Name == "foo").First();
            foreach (var cmd in foo.Blocks[0].Cmds)
                Assert.AreEqual(3, cmd.GetInstructionStatistics().Covered);

            Assert.AreEqual(3, (foo.Blocks[0].TransferCmd as ReturnCmd).GetInstructionStatistics().Covered);

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

            // The assume gets visited one extra time
            CheckBlockStartingWithAssumeCount(loopBody, 4, 3);

            var loopDone = main.Blocks[3];
            Assert.AreEqual("anon2_LoopDone", loopDone.Label);
            CheckBlockStartingWithAssumeCount(loopDone, 4, 1);

            // Check the goto of entry block
            var gotoStats = entryBlock.TransferCmd.GetInstructionStatistics() as GotoInstructionStatistics;
            Assert.AreEqual(1, gotoStats.TotalJumps);
            Assert.AreEqual(1, gotoStats.GetJumpsTo(loopHead));

            // Check the goto of loopHead
            var loopHeadGotoStats = loopHead.TransferCmd.GetInstructionStatistics() as GotoInstructionStatistics;
            Assert.AreEqual(4, loopHeadGotoStats.TotalJumps);
            Assert.AreEqual(1, loopHeadGotoStats.GetJumpsTo(loopDone));
            Assert.AreEqual(3, loopHeadGotoStats.GetJumpsTo(loopBody));

            // Check the goto of loopBody
            var loopBodyGotoStats = loopBody.TransferCmd.GetInstructionStatistics() as GotoInstructionStatistics;
            Assert.AreEqual(3, loopBodyGotoStats.TotalJumps);
            Assert.AreEqual(3, loopBodyGotoStats.GetJumpsTo(loopHead));
        }

        [Test()]
        public void NaiveGoto()
        {
            p = loadProgram("programs/InstructionStatistics.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = false;

            e.Run(getMain(p));

            // Check we executed foo three times
            var foo = p.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Name == "foo").First();
            foreach (var cmd in foo.Blocks[0].Cmds)
                Assert.AreEqual(3, cmd.GetInstructionStatistics().Covered);

            Assert.AreEqual(3, (foo.Blocks[0].TransferCmd as ReturnCmd).GetInstructionStatistics().Covered);

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

            // The assume gets visited one extra time
            CheckBlockStartingWithAssumeCount(loopBody, 4, 3);

            var loopDone = main.Blocks[3];
            Assert.AreEqual("anon2_LoopDone", loopDone.Label);
            CheckBlockStartingWithAssumeCount(loopDone, 4, 1);

            // Check the goto of entry block
            var gotoStats = entryBlock.TransferCmd.GetInstructionStatistics() as GotoInstructionStatistics;
            Assert.AreEqual(1, gotoStats.TotalJumps);
            Assert.AreEqual(1, gotoStats.GetJumpsTo(loopHead));

            // Check the goto of loopHead
            var loopHeadGotoStats = loopHead.TransferCmd.GetInstructionStatistics() as GotoInstructionStatistics;
            Assert.AreEqual(8, loopHeadGotoStats.TotalJumps);
            Assert.AreEqual(4, loopHeadGotoStats.GetJumpsTo(loopDone));
            Assert.AreEqual(4, loopHeadGotoStats.GetJumpsTo(loopBody));

            // Check the goto of loopBody
            var loopBodyGotoStats = loopBody.TransferCmd.GetInstructionStatistics() as GotoInstructionStatistics;
            Assert.AreEqual(3, loopBodyGotoStats.TotalJumps);
            Assert.AreEqual(3, loopBodyGotoStats.GetJumpsTo(loopHead));
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
    }
}

