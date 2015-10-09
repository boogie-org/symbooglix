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
using Symbooglix;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Linq;

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

        public static ProgramLocation GetModSetProgramLocation(this Procedure node)
        {
            return node.GetMetadata<ProgramLocation>( (int) Annotation.AnnotationIndex.PROGRAM_LOCATION_PROCEDURE_MODSET);
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

        // Extensions for computing coverage
        public static LineCoverage GetLineCoverage(this Block node)
        {
            var count = new LineCoverage();
            count.Reset();

            foreach (var cmd in node.Cmds)
            {
                count.TotalLines += 1;
                if (cmd.GetInstructionStatistics().Covered > 0)
                    count.CoveredLines += 1;
            }

            // Return command
            count.TotalLines += 1;
            if (node.TransferCmd.GetInstructionStatistics().Covered > 0)
                count.CoveredLines += 1;

            return count;
        }

        public static LineCoverage GetLineCoverage(this Implementation impl)
        {
            var count = new LineCoverage();
            count.Reset();

            foreach (var block in impl.Blocks)
            {
                count += block.GetLineCoverage();
            }

            return count;
        }

        public static LineCoverage GetLineCoverage(this Procedure proc)
        {
            var count = new LineCoverage();
            count.Reset();

            foreach (var requires in proc.Requires)
            {
                count.TotalLines += 1;
                if (requires.GetInstructionStatistics().Covered > 0)
                    count.CoveredLines += 1;
            }

            foreach (var ensures in proc.Ensures)
            {
                count.TotalLines += 1;
                if (ensures.GetInstructionStatistics().Covered > 0)
                    count.CoveredLines += 1;
            }

            return count;
        }

        public static LineCoverage GetLineCoverage(this Program prog)
        {
            var count = new LineCoverage();
            count.Reset();

            foreach (var axiom in prog.TopLevelDeclarations.OfType<Axiom>())
            {
                count.TotalLines += 1;
                if (axiom.GetInstructionStatistics().Covered > 0)
                    count.CoveredLines += 1;
            }

            foreach (var proc in prog.TopLevelDeclarations.OfType<Procedure>())
            {
                count += proc.GetLineCoverage();
            }

            foreach (var impl in prog.TopLevelDeclarations.OfType<Implementation>())
            {
                count += impl.GetLineCoverage();
            }

            return count;
        }

    }
}

