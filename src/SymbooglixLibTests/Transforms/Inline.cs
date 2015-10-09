//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using Microsoft.Boogie;
using NUnit.Framework;
using Symbooglix.Transform;
using SymbooglixLibTests;
using System;
using System.Linq;


namespace TransformTests
{
    [TestFixture()]
    public class Inline
    {
        [Test()]
        public void TestCase()
        {
            Program program = SymbooglixTest.LoadProgramFrom("Transforms/programs/simple_function_inline.bpl");

            var PM = new PassManager();
            PM.Add(new FunctionInliningPass());
            PM.Run(program);

            // Now check what we expected to be inlined was inlined

            // Another function that uses foo
            var barFunction = program.TopLevelDeclarations.OfType<Function>().Where(f => f.Name == "bar").First();
            Assert.AreEqual("(if x > 0 then x == 0 else x - 1 == 0)", barFunction.Body.ToString());

            // Axiom
            var axiom = program.TopLevelDeclarations.OfType<Axiom>().First();
            Assert.AreEqual("v == 0", axiom.Expr.ToString());


            var procedure = program.TopLevelDeclarations.OfType<Procedure>().First();

            // Requires
            Assert.AreEqual(1, procedure.Requires.Count);
            Assert.AreEqual("x == 0 && false <==> x == 0", procedure.Requires[0].Condition.ToString());

            // Ensures
            Assert.AreEqual(1, procedure.Ensures.Count);
            Assert.AreEqual("x == 0 <==> x == 0", procedure.Ensures[0].Condition.ToString());

            // Assert statement
            var assertCmd = program.TopLevelDeclarations.OfType<Implementation>().SelectMany(i => i.Blocks).SelectMany(cmd => cmd.Cmds).OfType<AssertCmd>().First();
            Assert.AreEqual("x == 0", assertCmd.Expr.ToString());
        }

        [Test()]
        public void InlineExistsWithFreeVariable()
        {
            Program program = SymbooglixTest.LoadProgramFrom("Transforms/programs/InlineExists.bpl");

            var PM = new PassManager();
            PM.Add(new FunctionInliningPass());
            PM.Run(program);

            // Check the requires on strLen
            var strLenProc = program.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.Name == "strLen").First();
            Assert.AreEqual("(exists x: int :: x >= 0 && s[x] == 0bv8)", strLenProc.Requires[0].Condition.ToString());
        }
    }


}

