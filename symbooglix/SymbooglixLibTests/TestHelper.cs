using symbooglix;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using Microsoft.Boogie;
using NUnit.Framework;

namespace SymbooglixLibTests
{
    public class TestHelper
    {
        public static Program loadProgram(String path)
        {
            // Debug log output goes to standard error.
            Debug.Listeners.Add(new TextWriterTraceListener(Console.Error));
            Assert.IsTrue(File.Exists(path));

            int errors = 0;
            Program p = null;
            List<String> defines = null;
            errors = Parser.Parse(path, defines, out p);
            Assert.IsTrue(errors == 0);
            Assert.IsTrue(p != null);

            // Type check?
            return p;
        }

        public static Executor getExecutor(Program p, IStateScheduler scheduler = null)
        {
            if (scheduler == null )
                scheduler = new DFSStateScheduler();

            Executor e = new Executor(p, scheduler);
            return e;
        }

        public static Implementation getMain(Program p)
        {
            var imp = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First();
            Assert.AreNotEqual(imp, null);
            return imp;
        }
    }
}

