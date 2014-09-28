﻿using NUnit.Framework;
using System;
using System.IO;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class InstructionPrinter : SymbooglixTest
    {
        [Test()]
        public void TestCase()
        {
            p = loadProgram("programs/assert_true.bpl");
            var SW = new StringWriter();
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());
            var printer = new Symbooglix.InstructionPrinter(SW);
            printer.Connect(e);

            e.Run(getMain(p));

            // FIXME: This is fragile
            Assert.AreEqual("programs/assert_true.bpl:3: [Cmd] assert true;\n" + 
                            "programs/assert_true.bpl:4: [TransferCmd] Microsoft.Boogie.ReturnCmd\n", SW.ToString());
        }
    }
}
