using System;
using Microsoft;
using System.Linq;
using Microsoft.Boogie;
using System.Diagnostics;


namespace symbooglix
{
    public class driver
    {
        public static int Main(String[] args)
        {
            if (args.Length == 0) {
                Console.WriteLine ("Pass boogie file as first arg!");
                return 1;
            }

            Debug.Listeners.Add(new TextWriterTraceListener(Console.Error));
            //Microsoft.Boogie.Program p = null;
            Program p = null;



            System.Collections.Generic.List<string> defines = null;
            int success = Parser.Parse (args[0], defines, out p);

            if (success != 0)
            {
                Console.WriteLine("Failed to parse");
                return 1;
            }

            IStateScheduler scheduler = new DFSStateScheduler();
            PrintingExecutor e = new PrintingExecutor(p, scheduler);

            // FIXME: Find a better way to choose entry point.
            Microsoft.Boogie.Implementation entry = p.TopLevelDeclarations.OfType<Implementation>().FirstOrDefault();

            return e.run(entry)? 1 : 0;



        }
    }
}

