﻿using System;
using Symbooglix;
using Microsoft.Boogie;
using System.Collections.Generic;

namespace Symbooglix
{
    public static class BoogieAbsyExtensions
    {
        // Handy extension to get ProgramLocation instaces from where we expect them to be
        // This implicitly depends on the AnnotationIndicies pass being run on the program
        // FIXME: This method should only be on instances (e.g. Cmds) that support having a 
        // ProgramLocation, applying to Absy is too broad!
        public static ProgramLocation GetProgramLocation(this Absy node)
        {
            return node.GetMetadata<ProgramLocation>( (int) Annotation.AnnotationIndex.PROGRAM_LOCATION);
        }

        // Handy accessor for metadata added by the OldExprCanonicaliser pass
        public static IList<GlobalVariable> GetOldExprVariables(this Procedure node)
        {
            return node.GetMetadata<IList<GlobalVariable>>((int) Annotation.AnnotationIndex.GLOBALS_USED_IN_OLD_EXPR);
        }

        // Handy accessor for metadata added by the OldExprCanonicaliser pass
        public static IList<GlobalVariable> GetOldExprVariables(this Implementation node)
        {
            return node.GetMetadata<IList<GlobalVariable>>((int) Annotation.AnnotationIndex.GLOBALS_USED_IN_OLD_EXPR);
        }

        public static InstructionStatistics GetInstructionStatistics(this Cmd node)
        {
            return node.GetMetadata<InstructionStatistics>((int) Annotation.AnnotationIndex.PROFILE_DATA);
        }

        public static InstructionStatistics GetInstructionStatistics(this TransferCmd node)
        {
            return node.GetMetadata<InstructionStatistics>((int) Annotation.AnnotationIndex.PROFILE_DATA);
        }

        public static InstructionStatistics GetInstructionStatistics(this Requires node)
        {
            return node.GetMetadata<InstructionStatistics>((int) Annotation.AnnotationIndex.PROFILE_DATA);
        }

        public static InstructionStatistics GetInstructionStatistics(this Ensures node)
        {
            return node.GetMetadata<InstructionStatistics>((int) Annotation.AnnotationIndex.PROFILE_DATA);
        }

        public static InstructionStatistics GetInstructionStatistics(this Axiom node)
        {
            return node.GetMetadata<InstructionStatistics>((int) Annotation.AnnotationIndex.PROFILE_DATA);
        }
    }
}

