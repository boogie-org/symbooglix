using System;
using System.Diagnostics;
using System.IO;
using Microsoft.Boogie;

namespace Symbooglix
{
    namespace Solver
    {
        // FIXME: Refactor this and SMTLIBQueryLoggingSolver
        public class SimpleSMTLIBSolver : ISolver
        {
            public int Timeout { get; private set;}
            protected SMTLIBQueryPrinter Printer = null;
            protected ConstraintManager currentConstraints = null;
            protected ProcessStartInfo StartInfo;
            private Result solverResult = Result.UNKNOWN;
            private bool receivedResult = false;
            private Process TheProcess = null;

            protected SimpleSMTLIBSolver(string PathToSolverExecutable, string solverArguments)
            {
                if (! File.Exists(PathToSolverExecutable))
                    throw new SolverNotFoundException(PathToSolverExecutable);

                StartInfo = new ProcessStartInfo(PathToSolverExecutable);
                StartInfo.Arguments = solverArguments;
                StartInfo.RedirectStandardInput = true; // Neccessary so we can send our query
                StartInfo.RedirectStandardOutput = true; // Necessary so we can read the output
                StartInfo.RedirectStandardError = true;
                StartInfo.UseShellExecute = false; // C# docs say this is required

                // We create the process early so the printer has access to the TextWriter
                CreateNewProcess();

                Printer = new SMTLIBQueryPrinter(TheProcess.StandardInput, /*humanReadable=*/ false);
            }

            private void CreateNewProcess()
            {
                if (TheProcess != null)
                    TheProcess.Close();

                this.TheProcess = Process.Start(StartInfo);

                if (Printer == null)
                    Printer = new SMTLIBQueryPrinter(TheProcess.StandardInput, /*humanReadable=*/ false);
                else
                    Printer.changeOutput(TheProcess.StandardInput);


                // Register for asynchronous callbacks
                TheProcess.OutputDataReceived += OutputHandler;
                TheProcess.ErrorDataReceived += ErrorHandler;
                TheProcess.BeginOutputReadLine();
                TheProcess.BeginErrorReadLine();
            }

            public void SetConstraints(ConstraintManager cm)
            {
                Printer.clearDeclarations();

                // Let the printer find the declarations
                currentConstraints = cm;
                foreach (var constraint in cm.Constraints)
                {
                    Printer.addDeclarations(constraint);
                }
            }

            public void SetTimeout(int seconds)
            {
                if (seconds < 0)
                    throw new InvalidSolverTimeoutException();

                Timeout = seconds;
            }

            private void PrintDeclarationsAndConstraints()
            {
                Printer.printVariableDeclarations();
                Printer.printFunctionDeclarations();
                Printer.printCommentLine(currentConstraints.Constraints.Count.ToString() +  " Constraints");
                foreach (var constraint in currentConstraints.Constraints)
                {
                    Printer.printAssert(constraint);
                }
            }

            public Result IsQuerySat(Expr Query, out IAssignment assignment)
            {
                throw new NotImplementedException();
            }

            public Result IsQuerySat(Expr Query)
            {
                return doQuery(Query);
            }

            public Result IsNotQuerySat(Expr Query, out IAssignment assignment)
            {
                throw new NotImplementedException();
            }

            public Result IsNotQuerySat(Expr Query)
            {
                return doQuery(Expr.Not(Query));
            }

            // This is not thread safe!
            private Result doQuery(Expr QueryToPrint)
            {
                receivedResult = false;

                Printer.addDeclarations(QueryToPrint);

                // Assume the process has already been setup
                SetSolverOptions();
                PrintDeclarationsAndConstraints();
                Printer.printAssert(QueryToPrint);
                Printer.printCheckSat();

                if (Timeout > 0)
                    TheProcess.WaitForExit(Timeout * 1000);
                else
                    TheProcess.WaitForExit();

                if (!receivedResult)
                    throw new NoSolverResultException("Failed to get solver result!");

                CreateNewProcess(); // For next invocation

                return solverResult;
            }

            protected virtual void OutputHandler(object sendingProcess, DataReceivedEventArgs stdoutLine)
            {
                // The event handler might get called more than once.
                // In fact for Z3 we get called twice, first with the result
                // and then again with a blank line (why?)
                if (stdoutLine.Data.Length == 0 || receivedResult)
                    return;

                receivedResult = true;
                switch (stdoutLine.Data)
                {
                    case "sat":
                        solverResult = Result.SAT;
                        break;
                    case "unsat":
                        solverResult = Result.UNSAT;
                        break;
                    case "unknown":
                        solverResult = Result.UNKNOWN;
                        break;
                    default:
                        solverResult = Result.UNKNOWN;
                        Console.Error.WriteLine("ERROR: Solver output \"" + stdoutLine.Data + "\" not parsed correctly");
                        break;
                }

                Printer.printExit();
            }

            protected virtual void ErrorHandler(object sendingProcess, DataReceivedEventArgs  stderrLine)
            {
                if (stderrLine.Data.Length > 0)
                {
                    Console.Error.WriteLine("Solver error received:");
                    Console.Error.WriteLine(stderrLine.Data);
                }
            }

            protected virtual void SetSolverOptions()
            {
                // Subclasses to implement
            }
        }


        public class SolverNotFoundException : Exception
        {
            public SolverNotFoundException(string path) : base("The Solver \"" + path + "\" could not be found")
            {

            }
        }

        public class NoSolverResultException : Exception
        {
            public NoSolverResultException(string msg) : base(msg)
            {

            }
        }
    }
}

