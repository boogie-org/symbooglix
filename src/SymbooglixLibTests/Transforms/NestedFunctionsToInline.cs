using NUnit.Framework;
using System;
using Symbooglix;
using Symbooglix.Transform;
using Microsoft.Boogie;
using SymbooglixLibTests;
using System.Linq;

namespace TransformTests
{
    [TestFixture()]
    public class NestedFunctionsToInline
    {
        [Test()]
        public void TestCase()
        {
            Program program = SymbooglixTest.loadProgram("Transforms/programs/NestedFunctionsToInline.bpl");

            var PM = new PassManager(program);
            PM.Add(new FunctionInliningPass());
            PM.Run();

            // Check the Expression on the AssertCmd was inlined as expected
            var assert = SymbooglixTest.getMain(program).Blocks[0].Cmds[0] as AssertCmd;
            Assert.AreEqual("v + 1 + v + 1 + 1 == 12", assert.Expr.ToString());
        }
    }
}

