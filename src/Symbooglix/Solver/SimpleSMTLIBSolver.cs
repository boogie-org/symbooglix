using System;
using System.Diagnostics;
using System.IO;
using Microsoft.Boogie;

namespace Symbooglix
{
    namespace Solver
    {
        // FIXME: Refactor this and SMTLIBQueryLoggingSolver
        public class SimpleSMTLIBSolver : ISolverImpl
        {
            public int Timeout { get; private set;}
            protected SMTLIBQueryPrinter Printer = null;
            protected ConstraintManager CurrentConstraints = null;
            protected ProcessStartInfo StartInfo;
            private Result SolverResult = Result.UNKNOWN;
            private bool ReceivedResult = false;
            private Process TheProcess = null;
            private System.Text.Encoding TheEncoding = null;

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

                // This is a HACK
                TheEncoding = new System.Text.UTF8Encoding(/* encoderShouldEmitUTF8Identifier=*/ false);

                // We create the process early so the printer has access to the TextWriter
                CreateNewProcess();
            }

            private void CreateNewProcess()
            {
                if (TheProcess != null)
                    TheProcess.Close();

                this.TheProcess = Process.Start(StartInfo);

                if (Printer == null)
                    Printer = new SMTLIBQueryPrinter(GetStdInput(), /*humanReadable=*/ false);
                else
                    Printer.ChangeOutput(GetStdInput());


                // Register for asynchronous callbacks
                TheProcess.OutputDataReceived += OutputHandler;
                TheProcess.ErrorDataReceived += ErrorHandler;
                TheProcess.BeginOutputReadLine();
                TheProcess.BeginErrorReadLine();
            }

            private StreamWriter GetStdInput()
            {
                // This is a hack. It seems when running the NUnit tests the Byte-Order-Mark gets emitted but not in the driver and this
                // seems to be caused by how the Encoding is set up. We hack around this by using our own StreamWriter and always
                // set encoderShouldEmitUTF8Identifier to false
                var streamWriter = new StreamWriter(TheProcess.StandardInput.BaseStream, TheEncoding);
                streamWriter.AutoFlush = true;
                return streamWriter;
            }

            public void SetConstraints(ConstraintManager cm)
            {
                Printer.ClearDeclarations();

                // Let the printer find the declarations
                CurrentConstraints = cm;
                foreach (var constraint in cm.ConstraintExprs)
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
                Printer.PrintCommentLine(CurrentConstraints.Count.ToString() +  " Constraints");
                foreach (var constraint in CurrentConstraints.ConstraintExprs)
                {
                    Printer.PrintAssert(constraint);
                }
            }

            private Object DisposeLock = new object();
            private bool HasBeenDisposed = false;
            public void Dispose()
            {
                lock (DisposeLock)
                {
                    if (HasBeenDisposed)
                        return;

                    TheProcess.CancelErrorRead();
                    Console.WriteLine("Cancelled reading stderr");
                    TheProcess.CancelOutputRead();
                    Console.WriteLine("Cancelled reading stdout");
                    TheProcess.Kill();
                    Console.WriteLine("killed process");
                    lock (ComputeSatisfiabilityLock)
                    {
                        TheProcess.Dispose();
                        Console.WriteLine("Disposed of process");
                    }
                    HasBeenDisposed = true;
                }
            }

            // This is not thread safe!
            private Object ComputeSatisfiabilityLock = new object();
            public Tuple<Result, IAssignment> ComputeSatisfiability(Expr queryExpr, bool computeAssignment)
            {
                lock (ComputeSatisfiabilityLock)
                {
                    ReceivedResult = false;

                    Printer.AddDeclarations(queryExpr);

                    // Assume the process has already been setup
                    try
                    {
                        SetSolverOptions();
                        PrintDeclarationsAndConstraints();
                        Printer.PrintAssert(queryExpr);
                        Printer.PrintCheckSat();
                    }
                    catch(System.IO.IOException)
                    {
                        // This might happen if the process gets killed whilst we are trying to write
                        if (!ReceivedResult)
                            throw new NoSolverResultException("Failed to get solver result!");
                    }


                    if (computeAssignment)
                        throw new NotSupportedException("Can't handle assignments yet");

                    if (Timeout > 0)
                        TheProcess.WaitForExit(Timeout * 1000);
                    else
                        TheProcess.WaitForExit();

                    if (!ReceivedResult)
                        throw new NoSolverResultException("Failed to get solver result!");

                    CreateNewProcess(); // For next invocation


                    return Tuple.Create(SolverResult, null as IAssignment);
                }
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

