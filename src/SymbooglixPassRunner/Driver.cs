//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using Symbooglix;
using System.Linq;
using System.Collections.Generic;
using CommandLine;
using CommandLine.Text;
using System.Text;
using Microsoft.Boogie;
using System.Diagnostics;
using Transform = Symbooglix.Transform;
using System.IO;

namespace SymbooglixPassRunner
{
    class MainClass
    {
        static PassBuilder PBuilder = new PassBuilder();
        public class CmdLineOpts
        {
            [Option("emit-before", DefaultValue = false, HelpText = "Emit Boogie program to stdout before running each pass")]
            public bool EmitProgramBefore { get; set; }

            [Option("emit-after", DefaultValue = false, HelpText = "Emit Boogie program to stdout before running each pass")]
            public bool EmitProgramAfter { get; set; }

            [OptionList('e', "entry-points",
                Separator = ',',
                DefaultValue = null,
                HelpText = "Comma seperated list of implementations to use as entry points for execution.")]
            public List<string> EntryPoints { get; set; }

            // FIXME: Urgh... how do you set the default value of the list?
            [OptionList('p', "passes",
                Separator = ',',
                DefaultValue = null,
                HelpText = "Comma seperated list of passes to run. Executed in left to right order")]
            public List<string> PassNames { get; set; }

            [Option('o', DefaultValue="", HelpText="Output path for Boogie program")]
            public string OutputPath { get; set; }

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
                    Heading = new HeadingInfo("Symbooglix Pass Runner", ""),
                    Copyright = new CopyrightInfo("Dan Liew", 2015),
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

                    help.AddPreOptionsLine("Usage: spr [options] <boogie program>");
                    help.AddOptions(this);
                    help.AddPostOptionsLine("");
                    help.AddPostOptionsLine("Passes:");

                    foreach (var passName in PBuilder.GetPassNames().OrderBy(s => s))
                    {
                        // FIXME: Show description too
                        help.AddPostOptionsLine(passName);
                    }
                    help.AddPostOptionsLine("");
                    help.AddPostOptionsLine("");
                }

                return help;
            }
        }

        public enum ExitCode
        {
            SUCCESS,
            COMMAND_LINE_ERROR,
            PARSE_ERROR,
            RESOLVE_ERROR,
            TYPECHECK_ERROR
        }

        private static void ExitWith(ExitCode exitCode)
        {
            Console.Error.WriteLine("Exiting with {0}", exitCode.ToString());
            System.Environment.Exit( (int) exitCode);
            throw new InvalidOperationException("Unreachable");
        }

        public static int Main(string[] args)
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
                Console.Error.WriteLine("Failed to parse args");
                ExitWith(ExitCode.COMMAND_LINE_ERROR);
            }

            if (options.boogieProgramPath == null)
            {
                Console.Error.WriteLine("A boogie program must be specified. See --help");
                ExitWith(ExitCode.COMMAND_LINE_ERROR);
            }

            if (!File.Exists(options.boogieProgramPath))
            {
                Console.WriteLine("Boogie program \"" + options.boogieProgramPath + "\" does not exist");
                ExitWith(ExitCode.COMMAND_LINE_ERROR);
            }

            // Load Boogie program

            Program program = null;

            int errors = Microsoft.Boogie.Parser.Parse(options.boogieProgramPath, /*defines=*/ new List<string>(), out program);

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


            // Start building passes
            var PM = new Symbooglix.Transform.PassManager();

            if (options.PassNames == null)
            {
                Console.Error.WriteLine("At least one pass must be specified");
                ExitWith(ExitCode.COMMAND_LINE_ERROR);
            }

            // Add the requested passes to the PassManager
            foreach (var passName in options.PassNames)
            {
                try
                {
                    var newPass = PBuilder.GetPass(passName, options);
                    PM.Add(newPass);
                }
                catch (NonExistantPassException)
                {
                    Console.Error.WriteLine("Pass {0} does not exist", passName);
                }
            }

            PM.BeforePassRun += delegate(Object passManager, Transform.PassManager.PassManagerEventArgs eventArgs)
            {
                Console.ForegroundColor = ConsoleColor.Red;
                Console.Error.WriteLine("Running pass " + eventArgs.ThePass.GetName());
                Console.ResetColor();
                if (options.EmitProgramBefore)
                {
                    Console.Error.WriteLine("**** Program before pass:");
                    Symbooglix.Util.ProgramPrinter.Print(eventArgs.TheProgram, Console.Error, /*pretty=*/true, Symbooglix.Util.ProgramPrinter.PrintType.UNSTRUCTURED_ONLY);
                    Console.Error.WriteLine("**** END Program before pass");
                }
            };

            PM.AfterPassRun += delegate(Object passManager, Transform.PassManager.PassManagerEventArgs eventArgs)
            {
                Console.ForegroundColor = ConsoleColor.Green;
                Console.Error.WriteLine("Finished running pass " + eventArgs.ThePass.GetName());
                Console.ResetColor();
                if (options.EmitProgramAfter)
                {
                    Console.Error.WriteLine("**** Program after pass:");
                    Symbooglix.Util.ProgramPrinter.Print(eventArgs.TheProgram, Console.Error, /*pretty=*/true, Symbooglix.Util.ProgramPrinter.PrintType.UNSTRUCTURED_ONLY);
                    Console.Error.WriteLine("**** END Program after pass:");
                }
            };

            // Run pass manager
            PM.Run(program);

            // Emit the program
            if (options.OutputPath.Length == 0)
            {
                // Write to stdout
                Console.Error.WriteLine("Writing output to stdout");
                Symbooglix.Util.ProgramPrinter.Print(program, Console.Out, /*pretty=*/true, Symbooglix.Util.ProgramPrinter.PrintType.UNSTRUCTURED_ONLY);
            }
            else
            {
                // Write to file
                Console.Error.WriteLine("Writing output to {0}", options.OutputPath);
                using (var TW = new  StreamWriter(options.OutputPath))
                {
                    Symbooglix.Util.ProgramPrinter.Print(program, TW, /*pretty=*/true, Symbooglix.Util.ProgramPrinter.PrintType.UNSTRUCTURED_ONLY);
                }
            }

            return (int)ExitCode.SUCCESS;
        }


        internal class PassBuilder
        {
            private Dictionary<string, System.Type> Map = new Dictionary<string, System.Type>();
            public PassBuilder()
            {
                var types = GetPassTypes();
                foreach (var type in types)
                {
                    Map.Add(StripSymbooglixPrefix(type.ToString()), type);
                }
            }

            public Symbooglix.Transform.IPass GetPass(string name, CmdLineOpts cmdLine)
            {
                // Passes without default constructors
                if (name == StripSymbooglixPrefix(typeof(Transform.AxiomAndEntryRequiresCheckTransformPass).ToString()))
                {
                    // This pass needs to know the entry points
                    if (cmdLine.EntryPoints == null)
                    {
                        Console.Error.WriteLine("Entry points must be specified to use AxiomAndEntryRequiresCheckTransformPass");
                        ExitWith(ExitCode.COMMAND_LINE_ERROR);
                    }

                    Predicate<Implementation> isEntryPoint = delegate(Implementation impl)
                    {
                        foreach (var entryPointName in cmdLine.EntryPoints)
                        {
                            if (impl.Name == entryPointName)
                                return true;
                        }

                        return false;
                    };

                    return new Transform.AxiomAndEntryRequiresCheckTransformPass(isEntryPoint);
                }

                // Passes with default constructors
                try
                {
                    var passType = Map[name];
                    return (Symbooglix.Transform.IPass) Activator.CreateInstance(passType);
                }
                catch (KeyNotFoundException)
                {
                    throw new NonExistantPassException();
                }
            }

            public IEnumerable<string> GetPassNames()
            {
                return Map.Keys;
            }

            public static string StripSymbooglixPrefix(string passName)
            {
                int dotPosition =  passName.IndexOf('.');
                if (dotPosition == -1)
                    throw new Exception("Passname is wrong");
                return passName.Substring(dotPosition +1);
            }

            public static IList<System.Type> GetPassTypes()
            {
                var passInterfaceType = typeof(Symbooglix.Transform.IPass);
                var typeList = new List<System.Type>();
                var types = AppDomain.CurrentDomain.GetAssemblies().SelectMany(s => s.GetTypes()).Where(p => passInterfaceType.IsAssignableFrom(p));
                foreach (var t in types)
                {
                    if (t == passInterfaceType)
                        continue;

                    typeList.Add(t);
                }
                return typeList;
            }
        }

        class NonExistantPassException : Exception
        {
            public NonExistantPassException() : base() { }
        }
    }

}
