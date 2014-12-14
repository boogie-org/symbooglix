using Microsoft.Boogie;
using NUnit.Framework;
using System;
using Symbooglix.Transform;
using System.Linq;
using System.Collections.Generic;

namespace TransformTests
{
    [TestFixture()]
    public class UniqueVariableEnforcing
    {
        [Test()]
        public void NoUniques()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
            const a:int;
            const b:int;
            ", "test.bpl");

            Assert.AreEqual(0, GetAxioms(prog).Count());
            var UVEP = RunUniqueVariableEnforcing(prog);
            Assert.AreEqual(0, GetAxioms(prog).Count());
            Assert.AreEqual(0, UVEP.AddedAxioms.Count());
        }

        [Test()]
        public void SingleUnique()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
            const unique a:int;
            const b:int;
            ", "test.bpl");

            Assert.AreEqual(0, GetAxioms(prog).Count());
            var UVEP = RunUniqueVariableEnforcing(prog);
            Assert.AreEqual(0, GetAxioms(prog).Count());
            Assert.AreEqual(0, UVEP.AddedAxioms.Count());
        }

        [Test()]
        public void TwoUniques()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
            const unique a:int;
            const unique b:int;
            ", "test.bpl");

            Assert.AreEqual(0, GetAxioms(prog).Count());
            var UVEP = RunUniqueVariableEnforcing(prog);
            Assert.AreEqual(1, GetAxioms(prog).Count());
            var axiom = GetAxioms(prog).First();
            Assert.AreEqual("a != b", axiom.Expr.ToString());

            Assert.AreEqual(1, UVEP.AddedAxioms.Count());
        }

        [Test()]
        public void ThreeUniques()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
            const unique a:int;
            const unique b:int;
            const unique c:int;
            ", "test.bpl");

            Assert.AreEqual(0, GetAxioms(prog).Count());
            var UVEP = RunUniqueVariableEnforcing(prog);
            Assert.AreEqual(1, GetAxioms(prog).Count());
            var axiom = GetAxioms(prog).First();
            Assert.AreEqual("a != b && a != c && b != c", axiom.Expr.ToString());

            Assert.AreEqual(1, UVEP.AddedAxioms.Count());
        }

        [Test()]
        public void FourUniques()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
            const unique a:int;
            const unique b:int;
            const unique c:int;
            const unique d:int;
            ", "test.bpl");

            Assert.AreEqual(0, GetAxioms(prog).Count());
            var UVEP = RunUniqueVariableEnforcing(prog);
            Assert.AreEqual(1, GetAxioms(prog).Count());
            var axiom = GetAxioms(prog).First();
            Assert.AreEqual("a != b && a != c && a != d && b != c && b != d && c != d", axiom.Expr.ToString());

            Assert.AreEqual(1, UVEP.AddedAxioms.Count());
        }

        [Test()]
        public void TwoUniquesWithOtherType()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
            const unique a:int;
            const unique b:int;

            const unique c:bool;
            ", "test.bpl");

            Assert.AreEqual(0, GetAxioms(prog).Count());
            var UVEP = RunUniqueVariableEnforcing(prog);
            Assert.AreEqual(1, GetAxioms(prog).Count());
            var axiom = GetAxioms(prog).First();
            Assert.AreEqual("a != b", axiom.Expr.ToString());

            Assert.AreEqual(1, UVEP.AddedAxioms.Count());
        }

        [Test()]
        public void TwoUniquesTypes()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
            const unique a:int;
            const unique b:int;

            const unique c:bool;
            const unique d:bool;
            ", "test.bpl");

            Assert.AreEqual(0, GetAxioms(prog).Count());
            var UVEP = RunUniqueVariableEnforcing(prog);
            Assert.AreEqual(2, GetAxioms(prog).Count());
            var axioms = GetAxioms(prog).ToList();
            Assert.AreEqual("a != b", axioms[0].Expr.ToString());
            Assert.AreEqual("c != d", axioms[1].Expr.ToString());

            Assert.AreEqual(2, UVEP.AddedAxioms.Count());
        }

        public UniqueVariableEnforcingPass RunUniqueVariableEnforcing(Program prog)
        {
            var PM = new PassManager();
            var UVEP = new UniqueVariableEnforcingPass();
            PM.Add(UVEP);
            PM.Run(prog);
            return UVEP;
        }

        public IEnumerable<Axiom> GetAxioms(Program prog)
        {
            return prog.TopLevelDeclarations.OfType<Axiom>();
        }
    }
}

