using System;
using System.Diagnostics;
using System.IO;
using Microsoft.Boogie;

namespace Symbooglix
{
    namespace Solver
    {
        // FIXME: Refactor this and SMTLIBQueryLoggingSolver
        public abstract class SimpleSMTLIBSolver : ISolver
        {
            public int Timeout { get; private set;}
            protected SMTLIBQueryPrinter Printer = null;
            protected ConstraintManager currentConstraints = null;
            protected ProcessStartInfo startInfo;
            private Result solverResult = Result.UNKNOWN;
            private bool receivedResult = false;

            public SimpleSMTLIBSolver(string PathToSolverExecutable)
            {
                if (! File.Exists(PathToSolverExecutable))
                    throw new SolverNotFoundException(PathToSolverExecutable);

                startInfo = new ProcessStartInfo(PathToSolverExecutable);
                startInfo.RedirectStandardInput = true; // Neccessary so we can send our query
                startInfo.RedirectStandardOutput = true; // Necessary so we can read the output
                startInfo.RedirectStandardError = true;
                startInfo.UseShellExecute = false; // C# docs say this is required

                // Subclasses should set the process arguments

                // We need to be careful to not print anything until we associate a TextWriter with the printer!
                Printer = new SMTLIBQueryPrinter(null, /*humanReadable=*/ false);
            }

            public void SetConstraints(ConstraintManager cm)
            {
                Printer.clearDeclarations();

                // Let the printer find the declarations
                currentConstraints = cm;
                foreach (var constraint in cm.constraints)
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

            private void printDeclarationsAndConstraints()
            {
                Printer.printVariableDeclarations();
                Printer.printFunctionDeclarations();
                Printer.printCommentLine(currentConstraints.constraints.Count.ToString() +  " Constraints");
                foreach (var constraint in currentConstraints.constraints)
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

                // Create Process
                var proc = Process.Start(startInfo);

                Printer.changeOutput(proc.StandardInput);

                // Register for asynchronous callback
                proc.OutputDataReceived += OutputHandler;
                proc.ErrorDataReceived += ErrorHandler;
                proc.BeginOutputReadLine();
                proc.BeginErrorReadLine();

                SetSolverOptions();
                printDeclarationsAndConstraints();
                Printer.printAssert(QueryToPrint);
                Printer.printCheckSat();

                if (Timeout > 0)
                    proc.WaitForExit(Timeout * 1000);
                else
                    proc.WaitForExit();

                if (!receivedResult)
                    throw new NoSolverResultException("Failed to get solver result!");

                proc.Close();

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

