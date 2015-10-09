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
using System.Collections.Generic;
using System.Linq;
using System;
using System.IO;

namespace BoogieTests
{
    [TestFixture()]
    public class BadTokenLocations
    {
        [Test()]
        public void TestCase()
        {
            // HACK
            CommandLineOptions.Install(new Microsoft.Boogie.CommandLineOptions());

            var path = "programs/locations.bpl";

            Assert.IsTrue(File.Exists(path));


            int errors = 0;
            Program p = null;
            List<String> defines = null;
            errors = Parser.Parse(path, defines, out p);
            Assert.AreEqual(0, errors);
            Assert.IsNotNull(p);

            // Resolve
            errors = p.Resolve();
            Assert.AreEqual(0, errors);

            // Type check
            errors = p.Typecheck();
            Assert.AreEqual(0, errors);

            // Pull out the assert command
            AssertCmd cmd = p.TopLevelDeclarations.OfType<Implementation>().First().Blocks.SelectMany(b => b.Cmds.OfType<AssertCmd>()).First();

            var token = cmd.tok;
            Assert.AreEqual(Path.GetFileName(token.filename), "locations.bpl");
            Assert.AreEqual(token.line, 3);

            // This is nasty. Triggering a ToString()
            // mucks up the Tokens in a buggy version
            // of Boogie!
            cmd.ToString();
            token = cmd.tok;

            Assert.AreEqual(Path.GetFileName(token.filename), "locations.bpl");
            Assert.AreEqual(token.line, 3);

        }
    }
}

