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
                DoSomethingWithProgramLocation(variable.GetProgramLocation());
            }

            // Check Procedures
            foreach (var proc in Prog.TopLevelDeclarations.OfType<Procedure>())
            {
                // TODO: Should Procedures have an associated ProgramLocation?
                //DoSomethingWithProgramLocation(proc.GetProgramLocation());

                foreach (var requires in proc.Requires)
                    DoSomethingWithProgramLocation(requires.GetProgramLocation());

                foreach (var ensures in proc.Ensures)
                    DoSomethingWithProgramLocation(ensures.GetProgramLocation());

                foreach (var inParam in proc.InParams)
                    DoSomethingWithProgramLocation(inParam.GetProgramLocation());

                foreach (var outParam in proc.OutParams)
                    DoSomethingWithProgramLocation(outParam.GetProgramLocation());

                DoSomethingWithProgramLocation(proc.GetModSetProgramLocation());
            }

            // Check Implementations
            foreach (var impl in Prog.TopLevelDeclarations.OfType<Implementation>())
            {
                // TODO: Should Implementations have an associated ProgramLocation?
                //DoSomethingWithProgramLocation(impl.GetProgramLocation());

                foreach (var inParam in impl.InParams)
                    DoSomethingWithProgramLocation(inParam.GetProgramLocation());

                foreach (var outParam in impl.OutParams)
                    DoSomethingWithProgramLocation(outParam.GetProgramLocation());

                foreach (var localVariable in impl.LocVars)
                    DoSomethingWithProgramLocation(localVariable.GetProgramLocation());
            }

            // Check basic blocks
            foreach (var bb in Prog.Blocks())
            {
                foreach (var cmd in bb.Cmds)
                    DoSomethingWithProgramLocation(cmd.GetProgramLocation());

                DoSomethingWithProgramLocation(bb.TransferCmd.GetProgramLocation());
            }
        }

        private void DoSomethingWithProgramLocation(ProgramLocation pl)
        {
            var plAsString = pl.ToString();
            Assert.IsNotEmpty(plAsString);
        }
    }
}

