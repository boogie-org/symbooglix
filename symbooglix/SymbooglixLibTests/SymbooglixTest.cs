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
    public abstract class SymbooglixTest
    {
        protected Program p;
        protected Executor e;

        public static Program loadProgram(String path)
        {
            // Debug log output goes to standard error.
            // Failing System.Diagnostics failures trigger NUnit assertion failures
            Debug.Listeners.Add(new AssertionTextWriterTraceListener(Console.Error));
            Assert.IsTrue(File.Exists(path));

            // THIS IS A HACK. Boogie's methods
            // depend on its command line parser being set!
            CommandLineOptions.Install(new SymbooglixCommandLineOptions());

            int errors = 0;
            Program p = null;
            List<String> defines = null;
            errors = Parser.Parse(path, defines, out p);
            Assert.AreEqual(errors, 0);
            Assert.IsNotNull(p);

            // Resolve
            errors = p.Resolve();
            Assert.AreEqual(errors, 0);

            // Type check
            errors = p.Typecheck();
            Assert.AreEqual(errors, 0);

            return p;
        }

        public static Executor getExecutor(Program p, IStateScheduler scheduler = null)
        {
            if (scheduler == null )
                scheduler = new DFSStateScheduler();

            Executor e = new Executor(p, scheduler);

            IExecutorHandler verifier = new VerifyUnmodifiedProcedureHandler();
            e.registerPreEventHandler(verifier);
            e.registerPostEventHandler(verifier);
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

