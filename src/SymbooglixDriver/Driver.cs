//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
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

            [Option("catch-exceptions", DefaultValue = 1, HelpText="Catch Exceptions")]
            public int CatchExceptions { get; set; }

            [Option("constant-caching", DefaultValue=1, HelpText="Cache constants when building expressions")]
            public int ConstantCaching { get; set; }

            [Option("concurrent-logging", DefaultValue = 1, HelpText = "Log files concurrently, otherwise do in serial")]
            public int ConcurrentLogging { get ; set; }

            [Option("check-entry-requires", DefaultValue = 1, HelpText="Check entry point requires")]
            public int CheckEntryRequires { get; set;}

            [Option("check-entry-axioms", DefaultValue = 1, HelpText="Check axioms")]
            public int CheckEntryAxioms { get; set;}

            [Option("check-unique-vars", DefaultValue = 1, HelpText="Check unique variables")]
            public int CheckUniqueVariableDecls { get; set;}

            [Option("emit-before", DefaultValue = false, HelpText = "Emit Boogie program to stdout before running each pass")]
            public bool emitProgramBefore { get; set; }

            [Option("emit-after", DefaultValue = false, HelpText = "Emit Boogie program to stdout before running each pass")]
            public bool emitProgramAfter { get; set; }

            [Option("emit-triggers", DefaultValue = 1, HelpText = "Emit quantifier triggers during execution (experimental). Default 1")]
            public int emitTriggers { get; set; }

            [Option("esi-show-constraints", DefaultValue = 0, HelpText = "If logging ExecutionState info as YAML then show constraints (Default: 0)")]
            public int ExecutionStateInfoShowConstraints { get; set; }

            [Option("esi-show-vars", DefaultValue = 0, HelpText = "If logging ExecutionState info as YAML then show variables (Default: 0)")]
            public int ExecutionStateInfoShowVariables { get; set; }

            [OptionList('D', "defines",Separator = ',', HelpText="Add defines to the Boogie parser. Each define should be seperated by a comma.")]
            public List<string> Defines { get; set; }

            // FIXME: Urgh... how do you set the default value of the list?
            [OptionList('e', "entry-points",
                        Separator = ',',
                        DefaultValue = null,
                        HelpText = "Comma seperated list of implementations to use as entry points for execution.")]
            public List<string> entryPoints { get; set; }

            [Option("stop-at-failure", DefaultValue=0, HelpText="Stop executor once N failures have been found. 0 means unlimited (Default 0)")]
            public int FailureLimit { get; set; }

            [Option("file-logging", DefaultValue=1, HelpText="Log information about execution to files (default=1)")]
            public int FileLogging { get; set ; }

            [Option("force-qfaufbv", DefaultValue= false, HelpText="HACK: Force solver to use qf_aufbv logic")]
            public bool ForceQFAUFBV { get; set; }

            [Option("fork-at-predicated-assign", DefaultValue = false, HelpText="Fork at predicated assign commands (v := if x then <expr> else v)")]
            public bool ForkAtPredicatedAssign { get; set; }

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

            [Option("log-terminated-state-info", DefaultValue=1, HelpText="Log information about a termination state to a YAML file (a value of 0 disables)")]
            public int LogTerminatedStateInfo { get; set;}

            [Option("log-non-terminated-state-info", DefaultValue=1, HelpText="Log information about a termination state to a YAML file (a value of 0 disables)")]
            public int LogNonTerminatedStateInfo { get; set;}

            [Option("caching-solver", DefaultValue=-1, HelpText="-1 do not use, 0 unlimited query cache, other query cache limited by specified number")]
            public int CachingSolver { get; set; }

            [Option("ci-solver", DefaultValue = 1, HelpText = "Use Constraint independence solver")]
            public int ConstraintIndepenceSolver { get; set; }

            [Option("max-depth", DefaultValue=-1, HelpText="Max ExplicitBranchDepth to explore. Default is -1 which means no limit")]
            public int MaxDepth { get; set; }

            [Option("max-loop-depth", DefaultValue = -1, HelpText = "Max loop depth to explore. Default is -1 which means no limit")]
            public int MaxLoopDepth { get; set; }

            [Option("print-instr", DefaultValue = false, HelpText = "Print instructions during execution")]
            public bool useInstructionPrinter { get; set; }

            [Option("prefer-loop-escaping-paths", DefaultValue =1, HelpText= "Prefer paths that escape loops (Default 1)")]
            public int PreferLoopEscapingPaths { get; set; }

            [Option("print-call-seq", DefaultValue = false, HelpText = "Print call sequence during execution")]
            public bool useCallSequencePrinter { get; set; }

            [Option("remove-trivial-assumes", DefaultValue= false, HelpText="Remove trivial assumes")]
            public bool RemoveTrivialAssumes { get; set; }

            [Option("skip-log-success-states", HelpText="Don't log information about states that terminate with success")]
            public bool SkipLogTerminatedWithSuccess { get; set; }

            [Option("skip-log-unsat-assume-states", HelpText="Don't log information about states that terminate with unsatisfiable assume")]
            public bool SkipLogTerminatedWithUnsatAssume { get; set; }

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

            [Option("persistent-solver", DefaultValue=1, HelpText="Try to make solver process persistent")]
            public int PersistentSolver { get; set; }

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

            [Option("symbolic-pool-cache", DefaultValue = 0, HelpText = "Use Symbolic pool cache (0 uses naive symbolic pool")]
            public int useSymbolicPoolCache { get ; set ; }

            [Option("write-smt2", DefaultValue = 1, HelpText="Write constraints for each ExecutionState as SMTLIBv2 (Default 1)")]
            public int WriteConstraints { get ; set; }

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
            NO_ERRORS_NO_TIMEOUT = 0, // Essentially means path exploration was exhaustive

            // Mono exits with exitcode 1 if there are uncaught exceptions so
            // we should use the same exit code when we catch them
            EXCEPTION_RAISED = 1,

            // For Executor
            ERRORS_NO_TIMEOUT = 2,
            NO_ERRORS_TIMEOUT,
            ERRORS_TIMEOUT,
            OUT_OF_MEMORY,
            NOT_IMPLEMENTED_EXCEPTION,
            NOT_SUPPORTED_EXCEPTION,
            INITIAL_STATE_TERMINATED,
            NO_ERRORS_NO_TIMEOUT_BUT_FOUND_SPECULATIVE_PATHS,
            NO_ERRORS_NO_TIMEOUT_BUT_HIT_BOUND,


            // Other stuff
            COMMAND_LINE_ERROR = 128,
            PARSE_ERROR,
            RESOLVE_ERROR,
            TYPECHECK_ERROR,
            RECURSIVE_FUNCTIONS_FOUND_ERROR,
            SOLVER_NOT_FOUND,
            ENTRY_POINT_NOT_FOUND_ERROR,
            CTRL_C_FORCED_EXIT,
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
            // This is for debugging
            bool catchExceptions = true;
            foreach (var arg in args)
            {
                // Look for --catch-exceptions=0
                if (arg == "--catch-exceptions=0")
                {
                    catchExceptions = false;
                    break;
                }
            }
            if (!catchExceptions)
            {
                Console.WriteLine("Not catching exceptions in the driver");
                return RealMain(args);
            }

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

        private static void SetupTerminationCatchers(Executor executor)
        {
            // Catch CTRL+C
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

            // Sending SIGINT to the driver when stdout/stderr is not attached to a TTY does not seem to
            // trigger the Coinsole.CancelKeyPress event. So here we use a HACK to catch the signals we
            // care about and ask the Executor to terminate
            var signals = new Mono.Unix.UnixSignal[] {
                new Mono.Unix.UnixSignal(Mono.Unix.Native.Signum.SIGTERM), // boogie-runner sends this
            };
            bool signalCaught = false;
            Task.Factory.StartNew(() =>
            {
                while (true)
                {
                    Console.WriteLine("Waiting for UNIX signals");
                    Mono.Unix.UnixSignal.WaitAny(signals);
                    Console.WriteLine("Caught UNIX signal");
                    if (signalCaught)
                    {
                        Console.WriteLine("Signal received again. Just exiting");
                        ExitWith(ExitCode.CTRL_C_FORCED_EXIT);
                    }
                    else
                    {
                        executor.Terminate(false);
                        signalCaught = true;
                    }
                }
            });
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

            if (options.FailureLimit < 0)
            {
                Console.Error.WriteLine("FailureLimit must be >= 0");
                ExitWith(ExitCode.COMMAND_LINE_ERROR);
            }


            Console.WriteLine("Using Scheduler: {0}", scheduler.ToString());

            var nonSpeculativeterminationCounter = new TerminationCounter(TerminationCounter.CountType.ONLY_NON_SPECULATIVE);
            var speculativeTerminationCounter = new TerminationCounter(TerminationCounter.CountType.ONLY_SPECULATIVE);
            IExprBuilder builder = new SimpleExprBuilder(/*immutable=*/ true);
            ISymbolicPool symbolicPool = null;
            if (options.useSymbolicPoolCache > 0)
            {
                throw new Exception("DON'T USE THIS. IT'S BROKEN");
                symbolicPool = new CachingSymbolicPool();
            }
            else
                symbolicPool = new SimpleSymbolicPool();

            Console.WriteLine("Using Symbolic Pool: {0}", symbolicPool.ToString());

            if (options.useConstantFolding > 0)
            {
                if (options.ConstantCaching > 0)
                {
                    Console.WriteLine("Using ConstantCachingExprBuilder");
                    builder = new ConstantCachingExprBuilder(builder);
                }

                builder = new ConstantFoldingExprBuilder(builder);
            }

            // Destroy the solver when we stop using it
            using (var solver = BuildSolverChain(options))
            {
                Executor executor = new Executor(program, scheduler, solver, builder, symbolicPool);

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

                if (options.gotoAssumeLookAhead > 0)
                {
                    executor.UseGotoLookAhead = true;
                }
                else
                {
                    executor.UseGotoLookAhead = false;
                }

                if (options.ForkAtPredicatedAssign)
                    executor.UseForkAtPredicatedAssign = true;

                if (options.CheckEntryRequires > 0)
                    executor.CheckEntryRequires = true;
                else
                {
                    Console.WriteLine("Warning: Requires at the entry point are not being checked");
                    executor.CheckEntryRequires = false;
                }

                if (options.CheckEntryAxioms > 0)
                    executor.CheckEntryAxioms = true;
                else
                {
                    Console.WriteLine("Warning: Axioms are not being checked");
                    executor.CheckEntryAxioms = false;
                }

                if (options.CheckUniqueVariableDecls > 0)
                    executor.CheckUniqueVariableDecls = true;
                else
                {
                    Console.WriteLine("Warning: Unique variables are not being checked");
                    executor.CheckUniqueVariableDecls = false;
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

                nonSpeculativeterminationCounter.Connect(executor);
                speculativeTerminationCounter.Connect(executor);

                if (options.FileLogging > 0)
                    SetupFileLoggers(options, executor, solver);

                SetupTerminationCatchers(executor);
                ApplyFilters(executor, options);

                if (options.FailureLimit > 0)
                {
                    var failureLimiter = new FailureLimiter(options.FailureLimit);
                    failureLimiter.Connect(executor);
                    Console.WriteLine("Using failure limit of {0}", options.FailureLimit);
                }

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
                catch (InitialStateTerminated)
                {
                    if (options.CatchExceptions == 0)
                    {
                        throw;
                    }
                    Console.ForegroundColor = ConsoleColor.Red;
                    Console.Error.WriteLine("The initial state terminated. Execution cannot continue");
                    Console.ResetColor();
                    ExitWith(ExitCode.INITIAL_STATE_TERMINATED);
                }
                catch (RecursiveFunctionDetectedException rfdException)
                {
                    if (options.CatchExceptions == 0)
                    {
                        throw;
                    }
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
                    if (options.CatchExceptions == 0)
                    {
                        throw;
                    }
                    Console.Error.WriteLine("Ran out of memory!");
                    Console.Error.WriteLine(e.ToString());
                    ExitWith(ExitCode.OUT_OF_MEMORY);
                }
                catch (NotImplementedException e)
                {
                    if (options.CatchExceptions == 0)
                    {
                        throw;
                    }
                    Console.Error.WriteLine("Feature not implemented!");
                    Console.Error.WriteLine(e.ToString());
                    ExitWith(ExitCode.NOT_IMPLEMENTED_EXCEPTION);
                }
                catch (NotSupportedException e)
                {
                    if (options.CatchExceptions == 0)
                    {
                        throw;
                    }
                    Console.Error.WriteLine("Feature not supported!");
                    Console.Error.WriteLine(e.ToString());
                    ExitWith(ExitCode.NOT_SUPPORTED_EXCEPTION);
                }


                Console.WriteLine("Finished executing");
                DumpStats(executor, solver, nonSpeculativeterminationCounter, speculativeTerminationCounter);
            }

            if (TimeoutHit)
            {
                ExitWith(nonSpeculativeterminationCounter.NumberOfFailures > 0 ? ExitCode.ERRORS_TIMEOUT : ExitCode.NO_ERRORS_TIMEOUT);
                throw new InvalidOperationException("Unreachable");
            }

            var exitCode = nonSpeculativeterminationCounter.NumberOfFailures > 0 ? ExitCode.ERRORS_NO_TIMEOUT : ExitCode.NO_ERRORS_NO_TIMEOUT;
            if (exitCode == ExitCode.NO_ERRORS_NO_TIMEOUT)
            {
                // If no errors were found we may need to pick a different exit code
                // because path exploration may not have been exhaustive due to speculative paths
                // or hitting a bound. This isn't perfect because we may hit a bound and have speculative
                // paths so we could use either exit code in this case.
                if (nonSpeculativeterminationCounter.DisallowedSpeculativePaths > 0 || speculativeTerminationCounter.NumberOfTerminatedStates > 0) {
                    exitCode = ExitCode.NO_ERRORS_NO_TIMEOUT_BUT_FOUND_SPECULATIVE_PATHS;
                    Console.WriteLine("NOTE: Bugs may have been missed!");
                }
                else if (nonSpeculativeterminationCounter.DisallowedPathDepths > 0) {
                    exitCode = ExitCode.NO_ERRORS_NO_TIMEOUT_BUT_HIT_BOUND;
                    Console.WriteLine("NOTE: Bugs may have been missed!");
                }
            }
            ExitWith(exitCode);
            return (int) exitCode; // This is required to keep the compiler happy.
        }

        public static void DumpStats(Executor executor, Solver.ISolver solver, TerminationCounter nonSpeculativeTerminationCounter,
            TerminationCounter speculativeTerminationCounter)
        {
            using (var ITW = new System.CodeDom.Compiler.IndentedTextWriter(Console.Out))
            {
                executor.Statistics.WriteAsYAML(ITW);
                solver.Statistics.WriteAsYAML(ITW);
                solver.SolverImpl.Statistics.WriteAsYAML(ITW);
                nonSpeculativeTerminationCounter.WriteAsYAML(ITW);
                speculativeTerminationCounter.WriteAsYAML(ITW);
            }
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
            //executorLogger.AddRootDirLogger(new MemoryUsageLogger()); // FIXME: Disable for experiments it is buggy
            executorLogger.AddRootDirLogger(new TerminationCounterLogger(TerminationCounter.CountType.ONLY_NON_SPECULATIVE));
            executorLogger.AddRootDirLogger(new TerminationCounterLogger(TerminationCounter.CountType.ONLY_SPECULATIVE));
            //executorLogger.AddRootDirLogger(new ExecutionTreeLogger(true));
            executorLogger.AddRootDirLogger(new ExecutorInfoLogger());

            Predicate<ExecutionState> statesToIgnoreFilter = delegate(ExecutionState state)
            {
                if (options.SkipLogTerminatedWithSuccess)
                {
                    if (state.TerminationType is TerminatedWithoutError)
                        return true; // Ignore
                }

                if (options.SkipLogTerminatedWithUnsatAssume)
                {
                    if (state.TerminationType is TerminatedAtUnsatisfiableAssume)
                        return true; // Ignore
                }

                return false;
            };

            bool concurrentLogging = options.ConcurrentLogging > 0;

            if (options.WriteConstraints > 0)
            {
                executorLogger.AddTerminatedStateDirLogger(new ExecutionStateConstraintLogger(ExecutionStateLogger.ExecutorEventType.TERMINATED_STATE,
                    statesToIgnoreFilter, concurrentLogging));
                executorLogger.AddTerminatedStateDirLogger(new ExecutionStateUnSatCoreLogger(ExecutionStateLogger.ExecutorEventType.TERMINATED_STATE,
                    statesToIgnoreFilter, concurrentLogging));

                executorLogger.AddNonTerminatedStateDirLogger(new ExecutionStateConstraintLogger(ExecutionStateLogger.ExecutorEventType.NON_TERMINATED_STATE_REMOVED,
                    statesToIgnoreFilter, concurrentLogging));
            }

            bool showConstraints = options.ExecutionStateInfoShowConstraints > 0;
            bool showVariables = options.ExecutionStateInfoShowVariables > 0;
            if (options.LogTerminatedStateInfo > 0)
            {
                executorLogger.AddTerminatedStateDirLogger(new ExecutionStateInfoLogger(ExecutionStateLogger.ExecutorEventType.TERMINATED_STATE,
                    showConstraints,
                    showVariables,
                    statesToIgnoreFilter,
                    concurrentLogging));
            }
            if (options.LogNonTerminatedStateInfo > 0)
            {
                executorLogger.AddNonTerminatedStateDirLogger(new ExecutionStateInfoLogger(ExecutionStateLogger.ExecutorEventType.NON_TERMINATED_STATE_REMOVED,
                    showConstraints,
                    showVariables,
                    statesToIgnoreFilter,
                    concurrentLogging));
            }

            executorLogger.Connect();

            Console.WriteLine("Logging to directory: " + executorLogger.RootDir.FullName);
        }

        public static Transform.PassManager GetPassManager(CmdLineOpts options)
        {
            // Supply our own PassManager for preparation so we can hook into its events
            var PM = new Transform.PassManager();

            if (options.RemoveTrivialAssumes)
                PM.Add(new Transform.TrivialAssumeElimination());

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

            if (options.MaxLoopDepth > 0)
                scheduler = new LimitLoopBoundScheduler(scheduler, options.MaxLoopDepth);

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
            var logicToUse = options.ForceQFAUFBV ? SMTLIBQueryPrinter.Logic.QF_AUFBV : SMTLIBQueryPrinter.Logic.DO_NOT_SET;

            switch (options.solver)
            {
                case CmdLineOpts.Solver.CVC4:
                    solverImpl = new Solver.CVC4SMTLIBSolver(options.UseNamedAttributes > 0,
                                                             options.pathToSolver,
                                                             options.PersistentSolver > 0,
                                                             options.emitTriggers > 0,
                                                             logicToUse);
                    break;
                case CmdLineOpts.Solver.Z3:
                    solverImpl = new Solver.Z3SMTLIBSolver(options.UseNamedAttributes > 0,
                                                           options.pathToSolver,
                                                           options.PersistentSolver > 0,
                                                           options.emitTriggers > 0,
                                                           logicToUse);
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

            if (options.CachingSolver >= 0)
            {
                solverImpl = new Solver.SimpleSolverCache(solverImpl, options.CachingSolver);
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

