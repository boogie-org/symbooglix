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
            p = LoadProgramFrom("programs/assert_true.bpl");
            var SW = new StringWriter();
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            var printer = new Symbooglix.InstructionPrinter(SW);
            printer.Connect(e);

            e.Run(GetMain(p));

            // FIXME: This is fragile
            Assert.AreEqual("programs/assert_true.bpl:3: [Cmd] assert true;" + Environment.NewLine +  
                            "programs/assert_true.bpl:4: [TransferCmd] return;" + Environment.NewLine, SW.ToString());
        }
    }
}

