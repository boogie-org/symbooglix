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
using System.Linq;
using Microsoft.Boogie;

namespace Symbooglix
{
    namespace Annotation
    {
        public class ProgramLocationAnnotater : Transform.IPass
        {
            public ProgramLocationAnnotater()
            {
            }

            public bool RunOn(Microsoft.Boogie.Program prog, Transform.PassInfo passInfo)
            {
                var visitor = new ProgramLocationAnnotationVisitor();
                prog = (Microsoft.Boogie.Program) visitor.Visit(prog);

                // We don't consider modifying metadata as changing the program
                return false;
            }

            public string GetName()
            {
                return "Program location annotater";
            }

            public void SetPassInfo(ref Transform.PassInfo passInfo)
            {
                return;
            }

            public void Reset()
            {
            }

        }

        class ProgramLocationAnnotationVisitor : StandardVisitor
        {
            public override Axiom VisitAxiom(Axiom axiom)
            {
                axiom.SetMetadata( (int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(axiom));
                return axiom; // No need to traverse deeper
            }

            public override Block VisitBlock(Block bb)
            {
                foreach (var cmd in bb.Cmds)
                    cmd.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(cmd));

                bb.TransferCmd.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(bb.TransferCmd));

                return bb; // No need to traverse deeper
            }

            public override Implementation VisitImplementation(Implementation impl)
            {
                foreach (var inParam in impl.InParams)
                    inParam.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(inParam));

                foreach (var outParam in impl.OutParams)
                    outParam.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(outParam));

                foreach (var local in impl.LocVars)
                    local.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(local));

                return base.VisitImplementation(impl); // Need to traverse deeper so basic blocks get traversed
            }

            public override Procedure VisitProcedure(Procedure procedure)
            {
                foreach (var require in procedure.Requires)
                    require.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(require));

                foreach (var ensure in procedure.Ensures)
                    ensure.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(ensure));

                // HACK: This is gross but the inParam and outParams on procedure are not the same
                // instances in Boogie. So we need to annotate those as well! Boogie really needs fixing!
                foreach (var inParam in procedure.InParams)
                    inParam.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(inParam));

                foreach (var outParam in procedure.OutParams)
                    outParam.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(outParam));

                // Modset
                procedure.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION_PROCEDURE_MODSET, new ProgramLocation(new ModifiesSet(procedure)));

                return procedure; // No need to traverse deeper
            }

            public override Constant VisitConstant(Constant variable)
            {
                variable.SetMetadata( (int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(variable));
                return variable;
            }

            public override GlobalVariable VisitGlobalVariable(GlobalVariable variable)
            {
                variable.SetMetadata( (int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(variable));
                return variable;
            }
        }
    }
}

