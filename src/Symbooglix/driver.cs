using CommandLine;
using CommandLine.Text;
using System;
using System.IO;
using Microsoft;
using System.Linq;
using Microsoft.Boogie;
using System.Diagnostics;
using System.Collections.Generic;



namespace Symbooglix
{
    public class driver
    {
        public class CmdLineOpts
        {
            [Option("append-query-log-file", DefaultValue = 0, HelpText = "When logging queries (see --log-queries) append to file rather than overwriting")]
            public int appendLoggedQueries { get; set; }

            [Option("dump-program", DefaultValue = "", HelpText = "Before execution write prepared program to file specified")]
            public string dumpProgramPath { get; set; }

            [Option("emit-before", DefaultValue = false, HelpText = "Emit Boogie program to stdout before running each pass")]
            public bool emitProgramBefore { get; set; }

            [Option("emit-after", DefaultValue = false, HelpText = "Emit Boogie program to stdout before running each pass")]
            public bool emitProgramAfter { get; set; }

            [OptionList('D', "defines",Separator = ',', HelpText="Add defines to the Boogie parser. Each define should be seperated by a comma.")]
            public List<string> Defines { get; set; }

            [Option('e', "entry-point", DefaultValue = "main", HelpText = "Implementation to use as the entry point for execution")]
            public string entryPoint { get; set; }

            // FIXME: Booleans can't be disabled in the CommandLine library so use ints instead
            [Option("fold-constants", DefaultValue = 1, HelpText = "Use Constant folding during execution")]
            public int useConstantFolding { get; set; }

            [Option("human-readable-smtlib", DefaultValue = 1, HelpText = "When writing SMTLIBv2 queries make them more readable by using indentation and comments")]
            public int humanReadable { get; set ;}

            [Option("log-queries", DefaultValue = "", HelpText= "Path to file to log queries to. Blank means logging is disabled.")]
            public string queryLogPath { get; set; }

            [Option("print-instr", DefaultValue = false, HelpText = "Print instructions during execution")]
            public bool useInstructionPrinter { get; set; }

            [Option("print-stack-enter-leave", DefaultValue = false, HelpText = "Print stackframe when entering/leaving procedures")]
            public bool useEnterLeaveStackPrinter { get; set; }

            [Option("print-call-seq", DefaultValue = false, HelpText = "Print call sequence during execution")]
            public bool useCallSequencePrinter { get; set; }

            public enum Solver
            {
                CVC4,
                DUMMY,
                Z3
            }

            // FIXME: The command line library should tell the user what are the valid values
            [Option("solver", DefaultValue = Solver.Z3, HelpText = "Solver to use (valid values CVC4, DUMMY, Z3)")]
            public Solver solver { get; set; }

            [Option("solver-path", DefaultValue = "", HelpText = "Path to the SMTLIBv2 solver")]
            public string pathToSolver { get; set; }

            [Option("verify-unmodified-impl", DefaultValue = true, HelpText = "Verify that implementation commands aren't accidently modified during execution")]
            public bool useVerifyUnmodifiedProcedureHandler { get; set; }

            [Option("use-modset-transform", DefaultValue = 1, HelpText = "Run the modset analysis to fix incorrect modsets before type checking")]
            public int useModSetTransform { get; set; }

            // Positional args
            [ValueOption(0)]
            public string boogieProgramPath { get; set; }

            // For printing parser error messages
            [ParserState]
            public IParserState LastParserState { get; set; }

           
            [HelpOption]
            public string GetUsage()
            {
                var help = new HelpText {
                    Heading = new HeadingInfo("Symbooglix", "The symbolic execution engine for boogie programs"),
                    Copyright = new CopyrightInfo("Dan Liew", 2014),
                    AdditionalNewLineAfterOption = true,
                    AddDashesToOption = true
                };

                // FIXME: Printing parser errors is totally broken.
                if (LastParserState == null)
                    Console.WriteLine("FIXME: CommandLine parser did not give state");

                if (LastParserState != null && LastParserState.Errors.Any())
                {
                    var errors = help.RenderParsingErrorsText(this, 2);
                    help.AddPostOptionsLine("Error: Failed to parse command line options");
                    help.AddPostOptionsLine(errors);
                }
                else
                {

                    help.AddPreOptionsLine("Usage: symbooglix [options] <boogie program>");
                    help.AddOptions(this);
                }

                return help;
            }
        }

        public static int Main(String[] args)
        {
            // Debug log output goes to standard error.
            Debug.Listeners.Add(new ExceptionThrowingTextWritierTraceListener(Console.Error));

            // FIXME: Urgh... we are forced to use Boogie's command line
            // parser becaue the Boogie program resolver/type checker
            // is dependent on the parser being used...EURGH!
            CommandLineOptions.Install(new Microsoft.Boogie.CommandLineOptions());


            var options = new CmdLineOpts();
            if (! CommandLine.Parser.Default.ParseArguments(args, options))
            {
                Console.WriteLine("Failed to parse args");
                return 1;
            }

            if (options.boogieProgramPath == null)
            {
                Console.WriteLine("A boogie program must be specified. See --help");
                return 1;
            }

            if (!File.Exists(options.boogieProgramPath))
            {
                Console.WriteLine("Boogie program \"" + options.boogieProgramPath + "\" does not exist");
                return 1;
            }

           
            Program p = null;

            if (options.Defines != null)
            {
                foreach (var define in options.Defines)
                    Console.WriteLine("Adding define \"" + define + "\" to Boogie parser");
            }

            int errors = Parser.Parse(options.boogieProgramPath, options.Defines, out p);

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

            if (options.useModSetTransform > 0)
            {
                // This is useful for Boogie Programs produced by the GPUVerify tool that
                // have had instrumentation added that invalidates the modset attached to
                // procedures. By running the analysis we may modify the modsets attached to
                // procedures in the program to be correct so that Boogie's Type checker doesn't
                // produce an error.
                var modsetAnalyser = new ModSetCollector();
                modsetAnalyser.DoModSetAnalysis(p);
            }

            errors = p.Typecheck();

            if (errors != 0)
            {
                Console.WriteLine("Failed to Typecheck.");
                return 1;
            }


            IStateScheduler scheduler = new DFSStateScheduler();

            // Destroy the solver when we stop using it
            using (var solver = BuildSolverChain(options))
            {
                Executor e = new Executor(p, scheduler, solver);
                Implementation entry = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == options.entryPoint).FirstOrDefault();
                if (entry == null)
                {
                    Console.WriteLine("Could not find implementation \"" + options.entryPoint + "\" to use as entry point");
                    return 1;
                }

                // This debugging handler should be registered first
                IExecutorHandler verifyUnmodified = null;
                if (options.useVerifyUnmodifiedProcedureHandler)
                {
                    verifyUnmodified = new VerifyUnmodifiedProcedureHandler();
                    e.RegisterPreEventHandler(verifyUnmodified);
                }

                if (options.useInstructionPrinter)
                {
                    Console.WriteLine("Installing instruction printer");
                    e.RegisterPreEventHandler(new InstructionPrinter());
                }

                if (options.useEnterLeaveStackPrinter)
                {
                    Console.WriteLine("Installing Entering and Leaving stack printer");
                    e.RegisterPreEventHandler(new EnterAndLeaveStackPrinter());
                }

                if (options.useCallSequencePrinter)
                {
                    Console.WriteLine("Installing call sequence printer");
                    e.RegisterPreEventHandler(new CallSequencePrinter());
                }

                if (options.useVerifyUnmodifiedProcedureHandler)
                {
                    // This debugging handler should be registered last
                    e.RegisterPostEventHandler(verifyUnmodified);
                }

                if (options.useConstantFolding > 0)
                {
                    e.UseConstantFolding = true;
                }
                else
                {
                    e.UseConstantFolding = false;
                }

                // Just print a message about break points for now.
                e.RegisterBreakPointHandler(new BreakPointPrinter());

                e.RegisterTerminationHandler(new TerminationConsoleReporter());

                // Supply our own PassManager for preparation so we can hook into its events
                var PM = new Transform.PassManager(p);

                // Use anonymous methods so we can use closure to read command line options
                Transform.PassManager.PassRunEvent beforePassHandler = delegate(Object passManager, Transform.PassManager.PassManagerEventArgs eventArgs)
                {
                    Console.ForegroundColor = ConsoleColor.Red;
                    Console.WriteLine("Running pass " + eventArgs.ThePass.GetName());
                    Console.ResetColor();
                    if (options.emitProgramBefore)
                    {
                        Console.WriteLine("**** Program before pass:");
                        Util.ProgramPrinter.Print(eventArgs.TheProgram, Console.Out, /*pretty=*/true);
                        Console.WriteLine("**** END Program before pass");
                    }
                };

                Transform.PassManager.PassRunEvent afterPassHandler = delegate(Object passManager, Transform.PassManager.PassManagerEventArgs eventArgs)
                {
                    Console.ForegroundColor = ConsoleColor.Green;
                    Console.WriteLine("Finished running pass " + eventArgs.ThePass.GetName());
                    Console.ResetColor();
                    if (options.emitProgramAfter)
                    {
                        Console.WriteLine("**** Program after pass:");
                        Util.ProgramPrinter.Print(eventArgs.TheProgram, Console.Out, /*pretty=*/true);
                        Console.WriteLine("**** END Program after pass:");
                    }
                };

                PM.BeforePassRun += beforePassHandler;
                PM.AfterPassRun += afterPassHandler;
                e.PrepareProgram(PM);

                // Write program to file if requested
                if (options.dumpProgramPath.Length > 0)
                {
                    Console.Out.WriteLine("Writing prepared program to \"" + options.dumpProgramPath + "\"");
                    using (StreamWriter outputFile = File.CreateText(options.dumpProgramPath))
                    {
                        // FIXME: Get program from executor.
                        Util.ProgramPrinter.Print(p, outputFile, /*pretty=*/true);
                    }
                }

                e.Run(entry);
                Console.WriteLine(solver.Statistics.ToString());
            }
            return 0;
        }

        public static Solver.ISolver BuildSolverChain(CmdLineOpts options)
        {
            Solver.ISolverImpl solverImpl = null;

            // Try to guess the location of executable. This is just for convenience
            if (options.pathToSolver.Length == 0 && options.solver != CmdLineOpts.Solver.DUMMY)
            {
                Console.WriteLine("Path to SMT solver not specified. Guessing location");

                // Look in the directory of the currently running executable for other solvers
                var pathToSolver = Path.Combine(Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location),
                                                options.solver.ToString().ToLower());

                if (File.Exists(pathToSolver))
                {
                    Console.WriteLine("Found \"{0}\"", pathToSolver);
                    options.pathToSolver = pathToSolver;
                }
                else
                {
                    // Try with ".exe" appended
                    pathToSolver = pathToSolver + ".exe";
                    if (File.Exists(pathToSolver))
                    {
                        Console.WriteLine("Found \"{0}\"", pathToSolver);
                        options.pathToSolver = pathToSolver;
                    }
                    else
                    {
                        Console.Error.WriteLine("Could not find \"{0}\" (also without .exe)", pathToSolver);
                        System.Environment.Exit(1);
                    }
                }
            }

            switch (options.solver)
            {
                case CmdLineOpts.Solver.CVC4:
                    solverImpl = new Solver.CVC4SMTLIBSolver(options.pathToSolver);
                    break;
                case CmdLineOpts.Solver.Z3:
                    solverImpl = new Solver.Z3SMTLIBSolver(options.pathToSolver);
                    break;
                case CmdLineOpts.Solver.DUMMY:
                    solverImpl = new Solver.DummySolver();
                    break;
                default:
                    throw new NotSupportedException("Unhandled solver type");
            }



            if (options.queryLogPath.Length > 0)
            {
                // FIXME: How are we going to ensure this file gets closed properly?
                StreamWriter QueryLogFile = new StreamWriter(options.queryLogPath, /*append=*/ options.appendLoggedQueries > 0);
                solverImpl = new Solver.SMTLIBQueryLoggingSolverImpl(solverImpl, QueryLogFile, options.humanReadable > 0);
            }

            // Only support this for now.
            Solver.ISolver solver = new Solver.SimpleSolver(solverImpl);
            return solver;
        }
    }
}

