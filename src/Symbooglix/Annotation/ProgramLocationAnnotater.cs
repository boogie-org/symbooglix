using System;
using Symbooglix;
using System.Linq;
using Microsoft.Boogie;

namespace Symbooglix
{
    namespace Annotation
    {
        public class ProgramLocationAnnotater : Transform.IProgramPass
        {
            public ProgramLocationAnnotater()
            {
            }

            public bool RunOn(Microsoft.Boogie.Program prog)
            {
                // FIXME: Factor these iterators out

                // Axioms
                foreach (var axiom in prog.TopLevelDeclarations.OfType<Axiom>())
                    axiom.SetMetadata( (int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(axiom));


                // Global variables
                foreach (var variable in prog.TopLevelDeclarations.OfType<Variable>())
                    variable.SetMetadata( (int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(variable));

                // Local variables in implementations
                foreach (var impl in prog.TopLevelDeclarations.OfType<Implementation>())
                {
                    foreach (var inParam in impl.InParams)
                        inParam.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(inParam));

                    foreach (var outParam in impl.OutParams)
                        outParam.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(outParam));

                    foreach (var local in impl.LocVars)
                        local.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(local));
                }

                // Requires, ensures and Modset on procedures
                foreach (var procedure in prog.TopLevelDeclarations.OfType<Procedure>())
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

                    // TODO: Modset
                }



                // Commands in basic blocks
                foreach (var bb in prog.Blocks())
                {
                    foreach (var cmd in bb.Cmds)
                        cmd.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(cmd));

                    bb.TransferCmd.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(bb.TransferCmd));
                }

                // We don't consider modifying metadata as changing the program
                return false;
            }

            public string GetName()
            {
                return "Program location annotater";
            }

            public void SetPassInfo(ref Transform.PassManager.PassInfo passInfo)
            {
                return;
            }
        }
    }
}

