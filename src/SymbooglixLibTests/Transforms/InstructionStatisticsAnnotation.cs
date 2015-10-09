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
using Microsoft.Boogie;
using SymbooglixLibTests;
using Symbooglix.Transform;
using System.Linq;
using Symbooglix;
using System.IO;

namespace TransformTests
{
    [TestFixture()]
    public class InstructionStatisticsAnnotation
    {
        private Program Prog;
        [Test()]
        public void TestCase()
        {
            Prog = SymbooglixTest.LoadProgramFrom("Transforms/programs/AnnotationPass.bpl");

            var pm = new PassManager();
            pm.Add(new Symbooglix.Annotation.InstructionStatisticsAnnotater());
            pm.Run(Prog);

            // Check Axioms
            foreach (var axiom in Prog.TopLevelDeclarations.OfType<Axiom>())
                DoSomethingWithInstructionStatistics(axiom.GetInstructionStatistics());


            // Check Procedures
            foreach (var proc in Prog.TopLevelDeclarations.OfType<Procedure>())
            {
                foreach (var requires in proc.Requires)
                    DoSomethingWithInstructionStatistics(requires.GetInstructionStatistics());

                foreach (var ensures in proc.Ensures)
                    DoSomethingWithInstructionStatistics(ensures.GetInstructionStatistics());
            }

            // Check basic blocks
            foreach (var bb in Prog.Blocks())
            {
                foreach (var cmd in bb.Cmds)
                    DoSomethingWithInstructionStatistics(cmd.GetInstructionStatistics());

                if (bb.TransferCmd is GotoCmd)
                {
                    var gotoCmd = bb.TransferCmd as GotoCmd;
                    var instrStats = gotoCmd.GetInstructionStatistics() as GotoInstructionStatistics;
                    Assert.AreEqual(0, instrStats.Covered);
                    Assert.AreEqual(0, instrStats.TotalJumps);

                    foreach (var target in gotoCmd.labelTargets)
                    {
                        Assert.AreEqual(0, instrStats.GetJumpsTo(target));
                    }
                }
                else
                    DoSomethingWithInstructionStatistics((bb.TransferCmd as ReturnCmd).GetInstructionStatistics());
            }
        }

        private void DoSomethingWithInstructionStatistics(InstructionStatistics instrStats)
        {
            Assert.AreEqual(0, instrStats.Covered);
            Assert.AreEqual(0, instrStats.Terminations);
            Assert.AreEqual(0, instrStats.Forks);
        }
    }
}

