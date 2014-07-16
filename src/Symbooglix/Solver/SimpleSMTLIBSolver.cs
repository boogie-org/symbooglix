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
            protected ConstraintManager CurrentConstraints = null;
            protected ProcessStartInfo StartInfo;
            private Result SolverResult = Result.UNKNOWN;
            private bool ReceivedResult = false;
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
            }

            private void CreateNewProcess()
            {
                if (TheProcess != null)
                    TheProcess.Close();

                this.TheProcess = Process.Start(StartInfo);

                if (Printer == null)
                    Printer = new SMTLIBQueryPrinter(TheProcess.StandardInput, /*humanReadable=*/ false);
                else
                    Printer.ChangeOutput(TheProcess.StandardInput);


                // Register for asynchronous callbacks
                TheProcess.OutputDataReceived += OutputHandler;
                TheProcess.ErrorDataReceived += ErrorHandler;
                TheProcess.BeginOutputReadLine();
                TheProcess.BeginErrorReadLine();
            }

            public void SetConstraints(ConstraintManager cm)
            {
                Printer.ClearDeclarations();

                // Let the printer find the declarations
                CurrentConstraints = cm;
                foreach (var constraint in cm.Constraints)
                {
                    Printer.AddDeclarations(constraint);
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
                Printer.PrintVariableDeclarations();
                Printer.PrintFunctionDeclarations();
                Printer.PrintCommentLine(CurrentConstraints.Constraints.Count.ToString() +  " Constraints");
                foreach (var constraint in CurrentConstraints.Constraints)
                {
                    Printer.PrintAssert(constraint);
                }
            }

            public Result IsQuerySat(Expr Query, out IAssignment assignment)
            {
                throw new NotImplementedException();
            }

            public Result IsQuerySat(Expr Query)
            {
                return DoQuery(Query);
            }

            public Result IsNotQuerySat(Expr Query, out IAssignment assignment)
            {
                throw new NotImplementedException();
            }

            public Result IsNotQuerySat(Expr Query)
            {
                return DoQuery(Expr.Not(Query));
            }

            // This is not thread safe!
            private Result DoQuery(Expr QueryToPrint)
            {
                ReceivedResult = false;

                Printer.AddDeclarations(QueryToPrint);

                // Assume the process has already been setup
                SetSolverOptions();
                PrintDeclarationsAndConstraints();
                Printer.PrintAssert(QueryToPrint);
                Printer.PrintCheckSat();

                if (Timeout > 0)
                    TheProcess.WaitForExit(Timeout * 1000);
                else
                    TheProcess.WaitForExit();

                if (!ReceivedResult)
                    throw new NoSolverResultException("Failed to get solver result!");

                CreateNewProcess(); // For next invocation

                return SolverResult;
            }

            protected virtual void OutputHandler(object sendingProcess, DataReceivedEventArgs stdoutLine)
            {
                // The event handler might get called more than once.
                // In fact for Z3 we get called twice, first with the result
                // and then again with a blank line (why?)
                if (stdoutLine.Data.Length == 0 || ReceivedResult)
                    return;

                ReceivedResult = true;
                switch (stdoutLine.Data)
                {
                    case "sat":
                        SolverResult = Result.SAT;
                        break;
                    case "unsat":
                        SolverResult = Result.UNSAT;
                        break;
                    case "unknown":
                        SolverResult = Result.UNKNOWN;
                        break;
                    default:
                        SolverResult = Result.UNKNOWN;
                        Console.Error.WriteLine("ERROR: Solver output \"" + stdoutLine.Data + "\" not parsed correctly");
                        break;
                }

                Printer.PrintExit();
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

