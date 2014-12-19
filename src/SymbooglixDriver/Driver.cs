using CommandLine;
using CommandLine.Text;
using System;
using System.IO;
using Microsoft;
using System.Linq;
using Microsoft.Boogie;
using Symbooglix;
using Solver = Symbooglix.Solver;
using Transform = Symbooglix.Transform;
using Util = Symbooglix.Util;
using System.Diagnostics;
using System.Collections.Generic;
using System.Threading;
using System.Threading.Tasks;



namespace SymbooglixDriver
{
    public class Driver
    {
        public class CmdLineOpts
        {
            [Option("append-query-log-file", DefaultValue = 0, HelpText = "When logging queries (see --log-queries) append to file rather than overwriting")]
            public int appendLoggedQueries { get; set; }

            [Option("emit-before", DefaultValue = false, HelpText = "Emit Boogie program to stdout before running each pass")]
            public bool emitProgramBefore { get; set; }

            [Option("emit-after", DefaultValue = false, HelpText = "Emit Boogie program to stdout before running each pass")]
            public bool emitProgramAfter { get; set; }

            [OptionList('D', "defines",Separator = ',', HelpText="Add defines to the Boogie parser. Each define should be seperated by a comma.")]
            public List<string> Defines { get; set; }

            // FIXME: Urgh... how do you set the default value of the list?
            [OptionList('e', "entry-points",
                        Separator = ',',
                        DefaultValue = null,
                        HelpText = "Comma seperated list of implementations to use as entry points for execution.")]
            public List<string> entryPoints { get; set; }

            [Option("file-logging", DefaultValue=1, HelpText="Log information about execution to files (default=1)")]
            public int FileLogging { get; set ; }

            [Option("force-qfabv", DefaultValue= false, HelpText="HACK: Force solver to use qf_abv logic")]
            public bool ForceQFABV { get; set; }

            [Option("goto-assume-look-ahead", DefaultValue= 1, HelpText="Prevent needless state creation and destruction by looking ahead at gotos")]
            public int gotoAssumeLookAhead { get; set; }

            [Option("gpuverify-entry-points", DefaultValue=false, HelpText = "Use GPUVerify kernels as entry points")]
            public bool gpuverifyEntryPoints { get; set; }

            [Option("gpuverify-ignore-invariants", DefaultValue=false, HelpText = "Ignore GPUVerify specific invariants")]
            public bool GPUverifyIgnoreInvariants { get; set; }

            [Option("globaldde", DefaultValue=1, HelpText="Run Global Dead Declaration eliminiation(default 1)")]
            public int GlobalDDE { get; set; }
              

            // FIXME: Booleans can't be disabled in the CommandLine library so use ints instead
            [Option("fold-constants", DefaultValue = 1, HelpText = "Use Constant folding during execution")]
            public int useConstantFolding { get; set; }

            [Option("human-readable-smtlib", DefaultValue = 1, HelpText = "When writing SMTLIBv2 queries make them more readable by using indentation and comments")]
            public int humanReadable { get; set ;}

            [Option("log-queries", DefaultValue = "", HelpText= "Path to file to log queries to. Blank means logging is disabled.")]
            public string queryLogPath { get; set; }

            [Option("ci-solver", DefaultValue = 1, HelpText = "Use Constraint independence solver")]
            public int ConstraintIndepenceSolver { get; set; }

            [Option("max-depth", DefaultValue=-1, HelpText="Max ExplicitBranchDepth to explore. Default is -1 which means no limit")]
            public int MaxDepth { get; set; }

            [Option("print-instr", DefaultValue = false, HelpText = "Print instructions during execution")]
            public bool useInstructionPrinter { get; set; }

            [Option("prefer-loop-escaping-paths", DefaultValue =1, HelpText= "Prefer paths that escape loops (Default 1)")]
            public int PreferLoopEscapingPaths { get; set; }

            [Option("print-call-seq", DefaultValue = false, HelpText = "Print call sequence during execution")]
            public bool useCallSequencePrinter { get; set; }

            [Option("timeout", DefaultValue=0, HelpText="Number of seconds to wait before killing executor for the current entry point")]
            public int timeout { get; set;}

            public enum Solver
            {
                CVC4,
                DUMMY,
                Z3
            }

            [Option("output-dir", DefaultValue="", HelpText="Directory to place Executor log files. By default a symbooglix-<N> directory is used")]
            public string outputDir { get; set; }

            public enum Scheduler
            {
                DFS,
                BFS,
                UntilEndBFS,
                AltBFS
            }

            [Option("scheduler", DefaultValue = Scheduler.DFS, HelpText="State scheduler to use")]
            public Scheduler scheduler { get; set; }

            // FIXME: The command line library should tell the user what are the valid values
            [Option("solver", DefaultValue = Solver.Z3, HelpText = "Solver to use (valid values CVC4, DUMMY, Z3)")]
            public Solver solver { get; set; }

            [Option("solver-path", DefaultValue = "", HelpText = "Path to the SMTLIBv2 solver")]
            public string pathToSolver { get; set; }

            [Option("solver-timeout", DefaultValue=120, HelpText="Maximum time allowed for a single query")]
            public int solverTimeout {get; set;}

            [Option("solver-use-named-attr", DefaultValue=1, HelpText="Use named attributes with SMTLIB based solvers")]
            public int UseNamedAttributes { get; set; }

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

        public enum ExitCode : int
        {
            // For Executor
            NO_ERRORS_NO_TIMEOUT = 0,
            ERRORS_NO_TIMEOUT,
            NO_ERRORS_TIMEOUT,
            ERRORS_TIMEOUT,
            OUT_OF_MEMORY,
            NOT_IMPLEMENTED_EXCEPTION,
            NOT_SUPPORTED_EXCEPTION,


            // Other stuff
            COMMAND_LINE_ERROR = 128,
            PARSE_ERROR,
            RESOLVE_ERROR,
            TYPECHECK_ERROR,
            RECURSIVE_FUNCTIONS_FOUND_ERROR,
            SOLVER_NOT_FOUND,
            ENTRY_POINT_NOT_FOUND_ERROR,
            CTRL_C_FORCED_EXIT,
            EXCEPTION_RAISED,
        }

        private static bool TimeoutHit = false;

        private static void ExitWith(ExitCode exitCode)
        {
            Console.WriteLine("Exiting with {0}", exitCode.ToString());
            System.Environment.Exit( (int) exitCode);
            throw new InvalidOperationException("Unreachable");
        }

        public static int Main(String[] args)
        {
            // We use this to capture if an unhandled exception was
            // raised and exit with the appropriate exit code if this happens.
            try
            {
                return RealMain(args);
            }
            catch (Exception e)
            {
                Console.Error.WriteLine("Exception raised");
                Console.Error.WriteLine(e.ToString());
                ExitWith(ExitCode.EXCEPTION_RAISED);
                return (int)ExitCode.EXCEPTION_RAISED; // Keep compiler happy
            }
        }

        public static int RealMain(String[] args)
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
                ExitWith(ExitCode.COMMAND_LINE_ERROR);
            }

            if (options.boogieProgramPath == null)
            {
                Console.WriteLine("A boogie program must be specified. See --help");
                ExitWith(ExitCode.COMMAND_LINE_ERROR);
            }

            if (!File.Exists(options.boogieProgramPath))
            {
                Console.WriteLine("Boogie program \"" + options.boogieProgramPath + "\" does not exist");
                ExitWith(ExitCode.COMMAND_LINE_ERROR);
            }

           
            Program program = null;

            if (options.Defines != null)
            {
                foreach (var define in options.Defines)
                    Console.WriteLine("Adding define \"" + define + "\" to Boogie parser");
            }

            int errors = Microsoft.Boogie.Parser.Parse(options.boogieProgramPath, options.Defines, out program);

            if (errors != 0)
            {
                Console.WriteLine("Failed to parse");
                ExitWith(ExitCode.PARSE_ERROR);
            }

            errors = program.Resolve();

            if (errors != 0)
            {
                Console.WriteLine("Failed to resolve.");
                ExitWith(ExitCode.RESOLVE_ERROR);
            }

            if (options.useModSetTransform > 0)
            {
                // This is useful for Boogie Programs produced by the GPUVerify tool that
                // have had instrumentation added that invalidates the modset attached to
                // procedures. By running the analysis we may modify the modsets attached to
                // procedures in the program to be correct so that Boogie's Type checker doesn't
                // produce an error.
                var modsetAnalyser = new ModSetCollector();
                modsetAnalyser.DoModSetAnalysis(program);
            }

            errors = program.Typecheck();

            if (errors != 0)
            {
                Console.WriteLine("Failed to Typecheck.");
                ExitWith(ExitCode.TYPECHECK_ERROR);
            }


            IStateScheduler scheduler = GetScheduler(options);

            // Limit Depth if necessary
            if (options.MaxDepth >= 0)
            {
                scheduler = new LimitExplicitDepthScheduler(scheduler, options.MaxDepth);
                Console.WriteLine("Using Depth limit:{0}", options.MaxDepth);
            }


            Console.WriteLine("Using Scheduler: {0}", scheduler.ToString());

            var terminationCounter = new TerminationCounter();
            // Destroy the solver when we stop using it
            using (var solver = BuildSolverChain(options))
            {
                Executor executor = new Executor(program, scheduler, solver);

                executor.ExecutorTimeoutReached += delegate(object sender, Executor.ExecutorTimeoutReachedArgs eventArgs)
                {
                    TimeoutHit = true; // Record so we can set the exitcode appropriately later
                    Console.Error.WriteLine("Timeout hit. Trying to kill Executor (may wait for solver)");
                };

                // Check all implementations exist and build list of entry points to execute
                var entryPoints = new List<Implementation>();

                // This is specific to GPUVerify
                if (options.gpuverifyEntryPoints)
                {
                    var kernels = program.TopLevelDeclarations.OfType<Implementation>().Where(impl => QKeyValue.FindBoolAttribute(impl.Attributes,"kernel"));
                    foreach (var kernel in kernels)
                    {
                        entryPoints.Add(kernel);
                    }

                    if (entryPoints.Count() == 0)
                    {
                        Console.WriteLine("Could not find any kernel entry points");
                        ExitWith(ExitCode.ENTRY_POINT_NOT_FOUND_ERROR);
                    }
                }
                else
                {
                    // Set main as default.
                    if (options.entryPoints == null)
                        options.entryPoints = new List<string>() { "main" };

                    foreach (var implString in options.entryPoints)
                    {
                        Implementation entry = program.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == implString).FirstOrDefault();
                        if (entry == null)
                        {
                            Console.WriteLine("Could not find implementation \"" + implString + "\" to use as entry point");
                            ExitWith(ExitCode.ENTRY_POINT_NOT_FOUND_ERROR);
                        }
                        entryPoints.Add(entry);
                    }
                }

                if (options.useInstructionPrinter)
                {
                    Console.WriteLine("Installing instruction printer");
                    var instrPrinter = new InstructionPrinter(Console.Out);
                    instrPrinter.Connect(executor);
                }

                if (options.useCallSequencePrinter)
                {
                    Console.WriteLine("Installing call sequence printer");
                    var callPrinter = new CallPrinter(Console.Out);
                    callPrinter.Connect(executor);
                }

                if (options.useConstantFolding > 0)
                {
                    executor.UseConstantFolding = true;
                }
                else
                {
                    executor.UseConstantFolding = false;
                }

                if (options.gotoAssumeLookAhead > 0)
                {
                    executor.UseGotoLookAhead = true;
                }
                else
                {
                    executor.UseGotoLookAhead = false;
                }

                if (options.GlobalDDE > 0)
                {
                    executor.UseGlobalDDE = true;
                    Console.WriteLine("WARNING: Using GlobalDDE. This may remove unsatisfiable axioms");
                }
                else
                    executor.UseGlobalDDE = false;

                // Just print a message about break points for now.
                executor.BreakPointReached += BreakPointPrinter.handleBreakPoint;

                // Write to the console about context changes
                var contextChangeReporter = new ContextChangedReporter();
                contextChangeReporter.Connect(executor);

                var stateHandler = new TerminationConsoleReporter();
                stateHandler.Connect(executor);

                terminationCounter.Connect(executor);

                if (options.FileLogging > 0)
                    SetupFileLoggers(options, executor, solver);

                bool hitCancelOnce = false;
                Console.CancelKeyPress += delegate(object sender, ConsoleCancelEventArgs eventArgs)
                {
                    if (hitCancelOnce)
                    {
                        Console.WriteLine("CTRL+C pressed again. Giving up and just exiting");
                        eventArgs.Cancel = false; // Force exit
                        ExitWith(ExitCode.CTRL_C_FORCED_EXIT);
                    }
                    else
                    {
                        hitCancelOnce = true;
                        Console.WriteLine("Received CTRL+C. Attempting to terminated Executor");
                        executor.Terminate(/*block=*/ false);
                        eventArgs.Cancel = true; // Don't exit yet
                    }
                };

                ApplyFilters(executor, options);

                try
                {
                    // Supply our own PassManager for preparation so we can hook into its events
                    executor.PreparationPassManager = GetPassManager(options);

                    foreach (var entryPoint in entryPoints)
                    {
                        Console.ForegroundColor = ConsoleColor.Cyan;
                        Console.WriteLine("Entering Implementation " + entryPoint.Name + " as entry point");
                        Console.ResetColor();
                        executor.Run(entryPoint, options.timeout);
                    }
                }
                catch (ExecuteTerminatedStateException)
                {
                    Console.ForegroundColor = ConsoleColor.Red;
                    Console.Error.WriteLine("The initial state terminated. Execution cannot continue");
                    Console.ResetColor();
                    ExitWith(ExitCode.ERRORS_NO_TIMEOUT);
                }
                catch (RecursiveFunctionDetectedException rfdException)
                {
                    Console.ForegroundColor = ConsoleColor.Red;
                    Console.Error.WriteLine("Detected the following recursive functions");
                    foreach (var function in rfdException.Functions)
                    {
                        Console.Error.Write(function.Name + ": ");
                        if (function.Body != null)
                            Console.Error.WriteLine(function.Body.ToString());

                        if (function.DefinitionAxiom != null)
                            Console.Error.WriteLine(function.DefinitionAxiom.Expr.ToString());
                    }
                    Console.ResetColor();
                    ExitWith(ExitCode.RECURSIVE_FUNCTIONS_FOUND_ERROR);
                }
                catch (OutOfMemoryException e)
                {
                    Console.Error.WriteLine("Ran out of memory!");
                    Console.Error.WriteLine(e.ToString());
                    ExitWith(ExitCode.OUT_OF_MEMORY);
                }
                catch (NotImplementedException e)
                {
                    Console.Error.WriteLine("Feature not implemented!");
                    Console.Error.WriteLine(e.ToString());
                    ExitWith(ExitCode.NOT_IMPLEMENTED_EXCEPTION);
                }
                catch (NotSupportedException e)
                {
                    Console.Error.WriteLine("Feature not supported!");
                    Console.Error.WriteLine(e.ToString());
                    ExitWith(ExitCode.NOT_SUPPORTED_EXCEPTION);
                }


                Console.WriteLine("Finished executing");
                Console.WriteLine(solver.Statistics.ToString());
                Console.WriteLine(terminationCounter.ToString());

                DumpOtherStats(executor, solver);
            }

            if (TimeoutHit)
            {
                ExitWith(terminationCounter.NumberOfFailures > 0 ? ExitCode.ERRORS_TIMEOUT : ExitCode.NO_ERRORS_TIMEOUT);
                throw new InvalidOperationException("Unreachable");
            }

            var exitCode = terminationCounter.NumberOfFailures > 0 ? ExitCode.ERRORS_NO_TIMEOUT : ExitCode.NO_ERRORS_NO_TIMEOUT;
            ExitWith(exitCode);
            return (int) exitCode; // This is required to keep the compiler happy.
        }

        public static void DumpOtherStats(Executor executor, Solver.ISolver solver)
        {
            var stats = solver.SolverImpl.Statistics;
            stats.Dump(Console.Out);
            executor.Statistics.Dump(Console.Out);
        }

        public static void SetupFileLoggers(CmdLineOpts options, Executor executor, Solver.ISolver solver)
        {
            ExecutorFileLoggerHandler executorLogger = null;
            if (options.outputDir.Length == 0)
                executorLogger = new ExecutorFileLoggerHandler(executor, Directory.GetCurrentDirectory(), /*makeDirectoryInPath=*/ true);
            else
                executorLogger = new ExecutorFileLoggerHandler(executor, options.outputDir, /*makeDirectoryInPath=*/ false);

            // Add our loggers
            executorLogger.AddRootDirLogger(new CallGrindFileLogger());
            executorLogger.AddRootDirLogger(new MemoryUsageLogger());
            executorLogger.AddRootDirLogger(new TerminationCounterLogger());
            executorLogger.AddRootDirLogger(new ExecutionTreeLogger(true));
            executorLogger.AddRootDirLogger(new SolverStatisticsLogger(solver));
            executorLogger.AddRootDirLogger(new ExecutorStatisticsLogger());

            executorLogger.AddTerminatedStateDirLogger(new ExecutionStateConstraintLogger(ExecutionStateLogger.ExecutorEventType.TERMINATED_STATE));
            executorLogger.AddTerminatedStateDirLogger(new ExecutionStateUnSatCoreLogger(ExecutionStateLogger.ExecutorEventType.TERMINATED_STATE));
            executorLogger.AddTerminatedStateDirLogger(new ExecutionStateInfoLogger(ExecutionStateLogger.ExecutorEventType.TERMINATED_STATE));

            executorLogger.AddNonTerminatedStateDirLogger(new ExecutionStateConstraintLogger(ExecutionStateLogger.ExecutorEventType.NON_TERMINATED_STATE_REMOVED));
            executorLogger.AddNonTerminatedStateDirLogger(new ExecutionStateInfoLogger(ExecutionStateLogger.ExecutorEventType.NON_TERMINATED_STATE_REMOVED));

            executorLogger.Connect();

            Console.WriteLine("Logging to directory: " + executorLogger.RootDir.FullName);
        }

        public static Transform.PassManager GetPassManager(CmdLineOpts options)
        {
            // Supply our own PassManager for preparation so we can hook into its events
            var PM = new Transform.PassManager();

            // Use anonymous methods so we can use closure to read command line options
            Transform.PassManager.PassRunEvent beforePassHandler = delegate(Object passManager, Transform.PassManager.PassManagerEventArgs eventArgs)
            {
                Console.ForegroundColor = ConsoleColor.Red;
                Console.WriteLine("Running pass " + eventArgs.ThePass.GetName());
                Console.ResetColor();
                if (options.emitProgramBefore)
                {
                    Console.WriteLine("**** Program before pass:");
                    Util.ProgramPrinter.Print(eventArgs.TheProgram, Console.Out, /*pretty=*/true, Symbooglix.Util.ProgramPrinter.PrintType.UNSTRUCTURED_ONLY);
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
                    Util.ProgramPrinter.Print(eventArgs.TheProgram, Console.Out, /*pretty=*/true, Symbooglix.Util.ProgramPrinter.PrintType.UNSTRUCTURED_ONLY);
                    Console.WriteLine("**** END Program after pass:");
                }
            };

            PM.BeforePassRun += beforePassHandler;
            PM.AfterPassRun += afterPassHandler;

            return PM;
        }

        public static IStateScheduler GetScheduler(CmdLineOpts options)
        {
            IStateScheduler scheduler = null;
            switch (options.scheduler)
            {
                case CmdLineOpts.Scheduler.DFS:
                    scheduler = new DFSStateScheduler();
                    break;
                case CmdLineOpts.Scheduler.BFS:
                    scheduler = new BFSStateScheduler();
                    break;
                case CmdLineOpts.Scheduler.UntilEndBFS:
                    scheduler = new UntilTerminationBFSStateScheduler();
                    break;
                case CmdLineOpts.Scheduler.AltBFS:
                    scheduler = new AlternativeBFSStateScheduler();
                    break;
                default:
                    throw new ArgumentException("Unsupported scheduler");
            }

            if (options.PreferLoopEscapingPaths > 0)
                scheduler = new LoopEscapingScheduler(scheduler);

            return scheduler;
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
                        ExitWith(ExitCode.SOLVER_NOT_FOUND);
                    }
                }
            }

            // HACK: THIS IS GROSS! REMOVE THIS ASAP AND FIND A CLEAN WAY OF DOING THIS!!!!!!!!!!!!
            var logicToUse = options.ForceQFABV ? SMTLIBQueryPrinter.Logic.QF_ABV : SMTLIBQueryPrinter.Logic.DO_NOT_SET;

            switch (options.solver)
            {
                case CmdLineOpts.Solver.CVC4:
                    solverImpl = new Solver.CVC4SMTLIBSolver(options.UseNamedAttributes > 0, options.pathToSolver, logicToUse);
                    break;
                case CmdLineOpts.Solver.Z3:
                    solverImpl = new Solver.Z3SMTLIBSolver(options.UseNamedAttributes > 0, options.pathToSolver, logicToUse);
                    break;
                case CmdLineOpts.Solver.DUMMY:
                    solverImpl = new Solver.DummySolver(Symbooglix.Solver.Result.UNKNOWN);
                    break;
                default:
                    throw new NotSupportedException("Unhandled solver type");
            }



            if (options.queryLogPath.Length > 0)
            {
                // FIXME: How are we going to ensure this file gets closed properly?
                StreamWriter QueryLogFile = new StreamWriter(options.queryLogPath, /*append=*/ options.appendLoggedQueries > 0);
                solverImpl = new Solver.SMTLIBQueryLoggingSolverImpl(solverImpl, QueryLogFile, /*useNamedAttributeBindings=*/true, options.humanReadable > 0);
            }

            if (options.ConstraintIndepenceSolver > 0)
            {
                solverImpl = new Solver.ConstraintIndependenceSolver(solverImpl);
            }

            // Only support this for now.
            Solver.ISolver solver = new Solver.SimpleSolver(solverImpl);
            solver.SetTimeout(options.solverTimeout);
            return solver;
        }

        public static void ApplyFilters(Executor executor, CmdLineOpts options)
        {
            if (!options.GPUverifyIgnoreInvariants)
                return;

            Console.ForegroundColor = ConsoleColor.DarkMagenta;
            Console.Error.WriteLine("WARNING: GPUVerify invariants will be ignored!");
            Console.ResetColor();

            executor.AssertFilter = (AssertCmd c) =>
            {
                if (QKeyValue.FindBoolAttribute(c.Attributes, "originated_from_invariant"))
                {
                    Console.ForegroundColor = ConsoleColor.DarkMagenta;
                    Console.Error.WriteLine("WARNING: Ignoring invariant {0}", c.ToString());
                    Console.ResetColor();
                    return false;
                }

                return true;
            };
        }
    }
}

