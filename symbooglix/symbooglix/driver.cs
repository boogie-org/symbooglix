using System;
using System.IO;
using Microsoft;
using System.Linq;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Collections.Generic;


namespace symbooglix
{
    public class driver
    {
        public static int Main(String[] args)
        {
            // Debug log output goes to standard error.
            Debug.Listeners.Add(new TextWriterTraceListener(Console.Error));

            // FIXME: Urgh... we are forced to use Boogie's command line
            // parser becaue the Boogie program resolver/type checker
            // is dependent on the parser being used...EURGH!
            CommandLineOptions.Install(new SymbooglixCommandLineOptions());
            if (!CommandLineOptions.Clo.Parse(args))
            {
                Console.WriteLine("Failed to parser command line arguments");
                return 1;
            }

            if (CommandLineOptions.Clo.Files.Count != 1)
            {
                Console.WriteLine("You must pass a single boogie program");
                return 1;
            }

            string boogieProgramPath = CommandLineOptions.Clo.Files [0];
			if (Path.GetExtension(boogieProgramPath) != ".bpl")
            {
                Console.WriteLine("The program should be a *.bpl file");
                return 1;
            }

            Program p = null;
            var defines = new List<String> { "FILE_0" }; // WTF??
            int errors = Parser.Parse (args[0], defines, out p);

            if (errors != 0)
            {
                Console.WriteLine("Failed to parse");
                return 1;
            }

            errors = p.Resolve();

            if (errors != 0)
            {
                Console.WriteLine("Failed to resolve.");
                return 1;
            }

            errors = p.Typecheck();

            if (errors != 0)
            {
                Console.WriteLine("Failed to resolve.");
                return 1;
            }


            IStateScheduler scheduler = new DFSStateScheduler();
            Executor e = new Executor(p, scheduler);

            // FIXME: Find a better way to choose entry point.
            Microsoft.Boogie.Implementation entry = p.TopLevelDeclarations.OfType<Implementation>().FirstOrDefault();

            return e.run(entry)? 1 : 0;



        }
    }
}

