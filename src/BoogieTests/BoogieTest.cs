//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2017 Daniel Liew
//
// This file is licensed under the MIT license.
// See LICENSE.txt for details.
//------------------------------------------------------------------------------
using Microsoft.Boogie;
using NUnit.Framework;
using SymbooglixLibTests; // FIXME: We shouldn't depend on this.
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;

namespace BoogieTests
{
    public class BoogieTest
    {
        public static void setupDebug()
        {
            // Debug log output goes to standard error.
            // Failing System.Diagnostics failures trigger NUnit assertion failures
            Debug.Listeners.Add(new AssertionTextWriterTraceListener(Console.Error));
        }

        public static void setupCmdLineParser()
        {
            // THIS IS A HACK. Boogie's methods
            // depend on its command line parser being set!
            CommandLineOptions.Install(new Microsoft.Boogie.CommandLineOptions());
        }

        public static Program loadProgram(String path)
        {
            setupDebug();
            Assert.IsTrue(File.Exists(path));

            setupCmdLineParser();

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

            return p;
        }
    }
}

