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
    public class ProgramLocationAnnotation
    {
        private Program Prog;
        [Test()]
        public void TestCase()
        {
            Prog = SymbooglixTest.LoadProgramFrom("Transforms/programs/AnnotationPass.bpl");

            var pm = new PassManager();
            pm.Add(new Symbooglix.Annotation.ProgramLocationAnnotater());
            pm.Run(Prog);

            // Check Variables (Global and constant)
            foreach (var variable in Prog.TopLevelDeclarations.OfType<Variable>())
            {
                CheckIsNotNullAndString(variable.GetProgramLocation());
                Assert.IsTrue(variable.GetProgramLocation().IsVariable);
            }

            // Check Procedures
            foreach (var proc in Prog.TopLevelDeclarations.OfType<Procedure>())
            {
                // TODO: Should Procedures have an associated ProgramLocation?
                //DoSomethingWithProgramLocation(proc.GetProgramLocation());

                foreach (var requires in proc.Requires)
                {
                    CheckIsNotNullAndString(requires.GetProgramLocation());
                    Assert.IsTrue(requires.GetProgramLocation().IsRequires);
                }

                foreach (var ensures in proc.Ensures)
                {
                    CheckIsNotNullAndString(ensures.GetProgramLocation());
                    Assert.IsTrue(ensures.GetProgramLocation().IsEnsures);
                }

                foreach (var inParam in proc.InParams)
                {
                    CheckIsNotNullAndString(inParam.GetProgramLocation());
                    Assert.IsTrue(inParam.GetProgramLocation().IsVariable);
                }

                foreach (var outParam in proc.OutParams)
                {
                    CheckIsNotNullAndString(outParam.GetProgramLocation());
                    Assert.IsTrue(outParam.GetProgramLocation().IsVariable);
                }

                CheckIsNotNullAndString(proc.GetModSetProgramLocation());
                Assert.IsTrue(proc.GetModSetProgramLocation().IsModifiesSet);
            }

            // Check Implementations
            foreach (var impl in Prog.TopLevelDeclarations.OfType<Implementation>())
            {
                // TODO: Should Implementations have an associated ProgramLocation?
                //DoSomethingWithProgramLocation(impl.GetProgramLocation());

                foreach (var inParam in impl.InParams)
                {
                    CheckIsNotNullAndString(inParam.GetProgramLocation());
                    Assert.IsTrue(inParam.GetProgramLocation().IsVariable);
                }

                foreach (var outParam in impl.OutParams)
                {
                    CheckIsNotNullAndString(outParam.GetProgramLocation());
                    Assert.IsTrue(outParam.GetProgramLocation().IsVariable);
                }

                foreach (var localVariable in impl.LocVars)
                {
                    CheckIsNotNullAndString(localVariable.GetProgramLocation());
                    Assert.IsTrue(localVariable.GetProgramLocation().IsVariable);
                }
            }

            // Check basic blocks
            foreach (var bb in Prog.Blocks())
            {
                foreach (var cmd in bb.Cmds)
                {
                    CheckIsNotNullAndString(cmd.GetProgramLocation());
                    Assert.IsTrue(cmd.GetProgramLocation().IsCmd);
                }

                CheckIsNotNullAndString(bb.TransferCmd.GetProgramLocation());
                Assert.IsTrue(bb.TransferCmd.GetProgramLocation().IsTransferCmd);
            }
        }

        private void CheckIsNotNullAndString(ProgramLocation pl)
        {
            Assert.IsNotNull(pl);
            Assert.IsNotNullOrEmpty(pl.ToString());
        }
    }
}

