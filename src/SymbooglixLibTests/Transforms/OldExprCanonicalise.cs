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
using Symbooglix;
using Symbooglix.Transform;
using SymbooglixLibTests;
using System.Linq;
using System.IO;

namespace TransformTests
{
    [TestFixture()]
    public class OldExprCanonicalise
    {
        private Program prog;
        private OldExprCanonicaliser pass;

        [Test()]
        public void MainEnsures()
        {
            LoadProgram();

            var main = prog.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First();
            Assert.AreEqual(1, main.Proc.Ensures.Count);
            Assert.AreEqual("g > old(g + 1)", main.Proc.Ensures[0].Condition.ToString());

            RunPass();

            Assert.AreEqual("g > old(g) + 1", main.Proc.Ensures[0].Condition.ToString());
        }

        [Test()]
        public void FooEnsures()
        {
            LoadProgram();

            var foo = prog.TopLevelDeclarations.OfType<Procedure>().Where(i => i.Name == "foo").First();
            Assert.AreEqual(2, foo.Ensures.Count);
            Assert.AreEqual("r == old(g)", foo.Ensures[0].Condition.ToString());
            Assert.AreEqual("g > old(g + old(2))", foo.Ensures[1].Condition.ToString());

            RunPass();

            Assert.AreEqual("r == old(g)", foo.Ensures[0].Condition.ToString());
            Assert.AreEqual("g > old(g) + 2", foo.Ensures[1].Condition.ToString());
        }

        [Test()]
        public void BarEnsures()
        {
            LoadProgram();
            var bar = prog.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "bar").First();
            Assert.AreEqual(2, bar.Proc.Ensures.Count);
            Assert.AreEqual("r == old(g)", bar.Proc.Ensures[0].Condition.ToString());
            Assert.AreEqual("g > old(g + old(g)) + old(g)", bar.Proc.Ensures[1].Condition.ToString());

            RunPass();

            Assert.AreEqual("r == old(g)", bar.Proc.Ensures[0].Condition.ToString());
            Assert.AreEqual("g > old(g) + old(g) + old(g)", bar.Proc.Ensures[1].Condition.ToString());
        }

        [Test()]
        public void BarBody()
        {
            LoadProgram();
            var bar = prog.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "bar").First();

            // temp := old(g + local);
            AssignCmd tempAssign = bar.Blocks[0].Cmds.OfType<AssignCmd>().Where( ac => ac.Lhss.Count == 1 && ac.Lhss[0].DeepAssignedVariable.Name == "temp").First();
            Assert.AreEqual("old(g + local)",tempAssign.Rhss[0].ToString());

            // g := g  + old(g);
            AssignCmd gAssignIfBlock = bar.Blocks[1].Cmds.OfType<AssignCmd>().Where( ac => ac.Lhss.Count == 1 && ac.Lhss[0].DeepAssignedVariable.Name == "g").First();
            Assert.AreEqual("g + old(g + h + 17) + h",gAssignIfBlock.Rhss[0].ToString());

            // g := g + old(old(old(g))) + 19;
            AssignCmd gAssignElseBlock = bar.Blocks[2].Cmds.OfType<AssignCmd>().Where( ac => ac.Lhss.Count == 1 && ac.Lhss[0].DeepAssignedVariable.Name == "g").First();
            Assert.AreEqual("g + old(old(old(g))) + 19",gAssignElseBlock.Rhss[0].ToString());

            // r := old(g);
            AssignCmd rAssign = bar.Blocks.SelectMany(bb => bb.Cmds).OfType<AssignCmd>().Where(ac => ac.Lhss.Count == 1 && ac.Lhss[0].DeepAssignedVariable.Name == "r").First();
            Assert.AreEqual("old(g)", rAssign.Rhss[0].ToString());

            RunPass();

            // temp := old(g + local);
            Assert.AreEqual("old(g) + local",tempAssign.Rhss[0].ToString());

            // g := g  + old(g);
            Assert.AreEqual("g + old(g) + old(h) + 17 + h",gAssignIfBlock.Rhss[0].ToString());

            // g := g + old(old(old(g))) + 19;
            Assert.AreEqual("g + old(g) + 19",gAssignElseBlock.Rhss[0].ToString());

            // r := old(g);
            Assert.AreEqual("old(g)", rAssign.Rhss[0].ToString());


        }


        [Test()]
        public void RecordedImplementationGlobals()
        {
            LoadProgram();
            RunPass();

            // This isn't counting the number of variables. It counts the number of implementations
            Assert.AreEqual(2, pass.GlobalsInsideOldExprUsedByImpl.Count);
            Assert.AreEqual(3, pass.GlobalsInsideOldExprUsedByProcedure.Count);

            // main
            var mainOldExprGlobals = pass.GlobalsInsideOldExprUsedByImpl.Where(kv => kv.Key.Name == "main").Select(kv => kv.Value).First();
            Assert.AreEqual(1, mainOldExprGlobals.Count);
            Assert.AreEqual("g", mainOldExprGlobals[0].Name);
            // Check metadata is set
            Assert.AreSame(mainOldExprGlobals, prog.TopLevelDeclarations.OfType<Implementation>().Where(impl => impl.Name == "main").First().GetOldExprVariables());

            // bar
            var barOldExprGlobals = pass.GlobalsInsideOldExprUsedByImpl.Where(kv => kv.Key.Name == "bar").Select(kv => kv.Value).First();
            Assert.AreEqual(2, barOldExprGlobals.Count);
            Assert.AreEqual(1, barOldExprGlobals.Where(globalV => globalV.Name == "g").Count());
            Assert.AreEqual(1, barOldExprGlobals.Where(globalV => globalV.Name == "h").Count());
            // Check metadata is set
            Assert.AreSame(barOldExprGlobals, prog.TopLevelDeclarations.OfType<Implementation>().Where(impl => impl.Name == "bar").First().GetOldExprVariables());
        }

        [Test()]
        public void RecordedProcedureGlobals()
        {
            LoadProgram();
            RunPass();

            // This isn't counting the number of variables. It counts the number of procedures
            Assert.AreEqual(3, pass.GlobalsInsideOldExprUsedByProcedure.Count);

            // main
            var mainOldExprGlobals = pass.GlobalsInsideOldExprUsedByProcedure.Where(kv => kv.Key.Name == "main").Select(kv => kv.Value).First();
            Assert.AreEqual(1, mainOldExprGlobals.Count);
            Assert.AreEqual("g", mainOldExprGlobals[0].Name);
            // Check metadata is set
            Assert.AreSame(mainOldExprGlobals, prog.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.Name == "main").First().GetOldExprVariables());

            // bar
            var barOldExprGlobals = pass.GlobalsInsideOldExprUsedByProcedure.Where(kv => kv.Key.Name == "bar").Select(kv => kv.Value).First();
            Assert.AreEqual(1, barOldExprGlobals.Count);
            Assert.AreEqual("g", barOldExprGlobals[0].Name);
            // Check metadata is set
            Assert.AreSame(barOldExprGlobals, prog.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.Name == "bar").First().GetOldExprVariables());

            // foo
            var fooOldExprGlobals = pass.GlobalsInsideOldExprUsedByProcedure.Where(kv => kv.Key.Name == "foo").Select(kv => kv.Value).First();
            Assert.AreEqual(1, fooOldExprGlobals.Count);
            Assert.AreEqual("g", fooOldExprGlobals[0].Name);
            // Check metadata is set
            Assert.AreSame(fooOldExprGlobals, prog.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.Name == "foo").First().GetOldExprVariables());
        }

        private void LoadProgram()
        {
            prog = SymbooglixTest.LoadProgramFrom("Transforms/programs/OldExprCanonicalise.bpl");
        }

        private void RunPass()
        {
            var PM = new PassManager();
            this.pass = new Symbooglix.Transform.OldExprCanonicaliser(/*annotateProceduresAndImplementations=*/ true);
            PM.Add(this.pass);
            PM.Run(prog);
        }
    }
}

