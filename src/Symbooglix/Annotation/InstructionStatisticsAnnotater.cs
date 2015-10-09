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

namespace Symbooglix
{
    namespace Annotation
    {
        public class InstructionStatisticsAnnotater : Transform.IPass
        {
            public InstructionStatisticsAnnotater()
            {
            }

            public string GetName()
            {
                return "Instruction Statistics Annotater";
            }

            public void SetPassInfo(ref Transform.PassInfo passInfo)
            {
                return; // No dependencies
            }

            public bool RunOn(Program prog, Symbooglix.Transform.PassInfo passInfo)
            {
                var visitor = new InstructionStatisticsAnnotatationVisitor();
                prog = (Program) visitor.Visit(prog);

                return false; // We don't consider adding annotations as modifying the program
            }

            public void Reset()
            {
            }
        }

        class InstructionStatisticsAnnotatationVisitor : ReadOnlyVisitor
        {
            public override Block VisitBlock(Block node)
            {
                foreach (var cmd in node.Cmds)
                    cmd.SetMetadata( (int) AnnotationIndex.PROFILE_DATA, new InstructionStatistics());

                if (node.TransferCmd is GotoCmd)
                    node.TransferCmd.SetMetadata( (int) AnnotationIndex.PROFILE_DATA, new GotoInstructionStatistics(node.TransferCmd as GotoCmd));
                else
                    node.TransferCmd.SetMetadata( (int) AnnotationIndex.PROFILE_DATA, new InstructionStatistics());

                return node; // No need to recurse deeper
            }

            public override Requires VisitRequires(Requires requires)
            {
                requires.SetMetadata( (int) AnnotationIndex.PROFILE_DATA, new InstructionStatistics());
                return requires; // No need to recurse deeper
            }

            public override Ensures VisitEnsures(Ensures ensures)
            {
                ensures.SetMetadata( (int) AnnotationIndex.PROFILE_DATA, new InstructionStatistics());
                return ensures; // No Need to recurse deeper
            }

            public override Axiom VisitAxiom (Axiom axiom)
            {
                axiom.SetMetadata( (int) AnnotationIndex.PROFILE_DATA, new InstructionStatistics());
                return axiom; // No Need to recurse deeper
            }
        }
    }
}

