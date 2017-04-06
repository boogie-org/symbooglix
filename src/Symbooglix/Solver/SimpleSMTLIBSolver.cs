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
using System.Diagnostics;
using System.IO;
using Microsoft.Boogie;
using System.Threading;

namespace Symbooglix
{
    namespace Solver
    {
        // FIXME: Refactor this and SMTLIBQueryLoggingSolver
        public class SimpleSMTLIBSolver : ISolverImpl
        {
            public int Timeout { get; private set;}
            protected SMTLIBQueryPrinter Printer = null;
            protected ProcessStartInfo StartInfo;
            private Result SolverResult = Result.UNKNOWN;
            private bool ReceivedResult = false;
            private Process TheProcess = null;
            private System.Text.Encoding TheEncoding = null;
            private SimpleSMTLIBSolverStatistics InternalStatistics;
            private Stopwatch ReadExprTimer;
            private Stopwatch SolverProcessTimer;
            private Stopwatch PrintExprTimer;
            private bool UseNamedAttributes;
            private bool SolverOptionsSet;
            private bool ReceivedError;
            public readonly bool PersistentProcess;
            private CountdownEvent ReceivedResultEvent;
            private bool Interrupted = false;
            private string SolverErrorMsg = "";

            // FIXME: This API sucks sooo much
            // Only has meaning if PersistentProcess is True
            protected bool UseReset;

            private bool EmitTriggers;

            protected SimpleSMTLIBSolver(bool useNamedAttributes, string PathToSolverExecutable, string solverArguments, bool persistentProcess, bool emitTriggers)
            {
                if (! File.Exists(PathToSolverExecutable))
                    throw new SolverNotFoundException(PathToSolverExecutable);

                SolverOptionsSet = false;
                ReceivedError = false;
                ReceivedResultEvent = null;
                this.PersistentProcess = persistentProcess;
                this.Timeout = 0;
                UseReset = false;
                EmitTriggers = emitTriggers;

                ReadExprTimer = new Stopwatch();
                SolverProcessTimer = new Stopwatch();
                PrintExprTimer = new Stopwatch();

                this.UseNamedAttributes = useNamedAttributes;

                InternalStatistics.Reset();

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

            public ISolverImplStatistics Statistics
            {
                get
                {
                    UpdateInternalStatistics(); // Only update the statistics when we really need to.
                    return InternalStatistics;
                }
            }

            private void UpdateInternalStatistics()
            {
                Debug.Assert(!ReadExprTimer.IsRunning && !SolverProcessTimer.IsRunning && !PrintExprTimer.IsRunning, "Tried to update statistics whilst timers were running");
                InternalStatistics.PrintExprTime = PrintExprTimer.Elapsed;
                InternalStatistics.ReadExprTime = ReadExprTimer.Elapsed;
                InternalStatistics.SolverProcessTime = SolverProcessTimer.Elapsed;
            }

            public void Interrupt()
            {
                // This is Gross
                Interrupted = true;

                if (PersistentProcess && ReceivedResultEvent != null)
                {
                    // Try to wake up sleeping
                    try
                    {
                        ReceivedResultEvent.Signal();
                    }
                    catch (Exception) { }
                }

                if (TheProcess == null || TheProcess.HasExited)
                    return;

                // If The process is running try to kill it
                try
                {
                    TheProcess.Kill();
                    TheProcess.Dispose();
                    // Incase the solver is asked to continue to function after being interrupted.
                    CreateNewProcess();
                }
                catch(Exception e)
                {
                    Console.WriteLine("FIXME: Exception throw whilst trying to interrupt");
                    Console.WriteLine(e.ToString());
                }
            }


            private void CreateNewProcess()
            {
                lock (DisposeLock)
                {
                    if (HasBeenDisposed)
                        return;

                    SolverProcessTimer.Start(); // Include the process setup time in solver execution time
                    if (TheProcess != null)
                    {
                        // Process.Close() does not kill the process
                        // so we need to kill it first if necessary
                        try
                        {
                            if (!TheProcess.HasExited)
                                TheProcess.Kill();
                        }
                        catch (InvalidOperationException)
                        {
                            // The process has not been started
                        }
                        catch (SystemException)
                        {
                            // No process to kill
                        }

                        TheProcess.Close();
                    }

                    ++InternalStatistics.ProcessCreationCount;

                    // HACK: When running in a NUnit test environment Console.Out.Encoding under Mono (4.0.4) is a UTF-8
                    // encoding with emission of the "Byte ordering mark" (BOM) enabled whereas in a normal executable
                    // environment the emission of the BOM is disabled. This causes problems because Z3 can't handle a
                    // BOM, therefore we want the emission of a BOM to always be disabled. It seems that when Mono sets
                    // up a process, it creates a pipe for the redirected input stream and it uses Console.Out.Encoding
                    // to set the encoding on the writable end of the pipe, therefore we want emission of the BOM to
                    // always be disabled on that stream. Modifying Console.OutputEncoding seems to acheieve this.
                    Console.OutputEncoding = TheEncoding;

                    this.TheProcess = Process.Start(StartInfo);

                    if (Printer == null)
                        Printer = new SMTLIBQueryPrinter(TheProcess.StandardInput, /*useNamedAttributeBindings*/UseNamedAttributes, /*humanReadable=*/false, /*printTriggers=*/EmitTriggers);
                    else
                        Printer.ChangeOutput(TheProcess.StandardInput);


                    // Register for asynchronous callbacks
                    TheProcess.OutputDataReceived += OutputHandler;
                    TheProcess.ErrorDataReceived += ErrorHandler;
                    TheProcess.BeginOutputReadLine();
                    TheProcess.BeginErrorReadLine();
                    SolverOptionsSet = false;
                    ReceivedResult = false;
                    SolverProcessTimer.Stop();
                }
            }

            public void SetTimeout(int seconds)
            {
                if (seconds < 0)
                    throw new InvalidSolverTimeoutException();

                Timeout = seconds;
            }

            private void PrintDeclarationsAndConstraints(IConstraintManager cm)
            {
                Printer.PrintSortDeclarations();
                Printer.PrintVariableDeclarations();
                Printer.PrintFunctionDeclarations();
                Printer.PrintCommentLine(cm.Count.ToString() +  " Constraints");
                foreach (var constraint in cm.ConstraintExprs)
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
                    try
                    {
                        TheProcess.CancelErrorRead();
                        Console.WriteLine("Cancelled reading stderr");
                        TheProcess.CancelOutputRead();
                        Console.WriteLine("Cancelled reading stdout");

                        if (!TheProcess.HasExited)
                            TheProcess.Kill();
                    }
                    catch (InvalidOperationException) {}

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
            public IQueryResult ComputeSatisfiability(Query query)
            {
                lock (ComputeSatisfiabilityLock)
                {
                    Interrupted = false;
                    ReceivedResult = false;
                    ReceivedError = false;
                    SolverResult = Result.UNKNOWN;
                    bool timeoutOccured = false;

                    try
                    {
                        // FIXME: This is only needed for PersistentProcess mode but we need
                        // to initialise it before we could get a response from the solver other we might race.
                        // In fact there still might be a race here...
                        using (ReceivedResultEvent = new CountdownEvent(1))
                        {
                            ReadExprTimer.Start();
                            Printer.ClearDeclarations();

                            // Let the printer find the declarations
                            foreach (var constraint in query.Constraints.Constraints)
                            {
                                Printer.AddDeclarations(constraint);
                            }
                            Printer.AddDeclarations(query.QueryExpr);
                            ReadExprTimer.Stop();

                            // Assume the process has already been setup
                            PrintExprTimer.Start();

                            // Set options if the current process hasn't been given them before or if we're using (reset)
                            if (!SolverOptionsSet || UseReset)
                            {
                                SetSolverOptions();
                                SolverOptionsSet = true;
                            }

                            if (PersistentProcess && !UseReset)
                                Printer.PrintPushDeclStack(1);

                            PrintDeclarationsAndConstraints(query.Constraints);
                            Printer.PrintAssert(query.QueryExpr.Condition);

                            // Start the timer for the process now. The solver should start processing as soon as we write (check-sat)
                            SolverProcessTimer.Start();

                            Printer.PrintCheckSat();
                            PrintExprTimer.Stop();

                            // Handle result
                            if (PersistentProcess)
                            {
                                // In persistent mode try to avoid killing the solver process so have to use
                                // a different synchronisation method to check if we've received a result

                                // Wait for result
                                if (Timeout > 0)
                                {
                                    timeoutOccured = !ReceivedResultEvent.Wait(Timeout * 1000);
                                }
                                else
                                    ReceivedResultEvent.Wait();

                                bool processExited = false;
                                try
                                {
                                    processExited = TheProcess.HasExited;
                                }
                                catch (InvalidOperationException)
                                {
                                    processExited = true;
                                }

                                if (ReceivedError && !Interrupted)
                                    throw new SolverErrorException(SolverErrorMsg);

                                if (!ReceivedResult || processExited || ReceivedResultEvent.CurrentCount > 0)
                                {
                                    // We don't know what state the process is in so we should kill it and make a fresh process
                                    SolverResult = Result.UNKNOWN;
                                    CreateNewProcess();
                                }
                                else
                                {
                                    // Clear all the declarations and assertions, ready for the next query
                                    if (UseReset)
                                    {
                                        Printer.PrintReset();
                                    }
                                    else
                                    {
                                        Printer.PrintPopDeclStack(1);
                                        Printer.Reset();
                                    }
                                }

                                if (SolverProcessTimer.IsRunning)
                                    SolverProcessTimer.Stop();
                            }
                            else
                            {
                                // Non-persistent process mode. We create and destroy a process for every query
                                if (Timeout > 0)
                                {
                                    timeoutOccured = !TheProcess.WaitForExit(Timeout * 1000);
                                }
                                else
                                    TheProcess.WaitForExit();

                                if (!ReceivedResult)
                                {
                                    Console.Error.WriteLine("Failed to get solver result!");
                                    SolverResult = Result.UNKNOWN;
                                }

                                if (ReceivedError && !Interrupted)
                                    throw new SolverErrorException(SolverErrorMsg);

                                if (SolverProcessTimer.IsRunning)
                                    SolverProcessTimer.Stop();

                                CreateNewProcess(); // For next invocation
                            }
                        }
                    }
                    catch (System.IO.IOException)
                    {
                        // This might happen if the process gets killed whilst we are trying to write
                        if (!ReceivedResult)
                        {
                            Console.Error.WriteLine("Failed to get solver result!");
                            SolverResult = Result.UNKNOWN;
                        }

                    }
                    catch (ObjectDisposedException)
                    {
                        Console.Error.WriteLine("Warning hit ObjectDisposedException. Assuming we are being disposed of!");
                        // Race condition, We got killed while trying to print. Just give up!
                        SolverResult = Result.UNKNOWN;
                    }
                    catch (UnauthorizedAccessException)
                    {
                        Console.Error.WriteLine("Warning hit UnauthorizedAccessException. Just returning unknown");
                        SolverResult = Result.UNKNOWN;
                    }
                    catch (System.NotSupportedException excep)
                    {
                        if (!Interrupted)
                            throw excep;
                        // Apparently this can be thrown if the process gets killed whilst writing
                        // System.NotSupportedException: Stream does not support writing
                        Console.Error.WriteLine("Warning hit System.NotSupportedException. Just returning unknown");
                        SolverResult = Result.UNKNOWN;
                    }

                    ReceivedResultEvent = null;

                    if (timeoutOccured)
                        ++InternalStatistics.TimeoutCount;

                    // FIXME: We need to implement our own class so we can support assignments and the unsat core
                    return new SimpleQueryResult(SolverResult);
                }
            }

            protected virtual void OutputHandler(object sendingProcess, DataReceivedEventArgs stdoutLine)
            {
                // The event handler might get called more than once.
                // In fact for Z3 we get called twice, first with the result
                // and then again with a blank line (why?)
                if (String.IsNullOrEmpty(stdoutLine.Data) || ReceivedResult)
                    return;

                switch (stdoutLine.Data)
                {
                    case "sat":
                        SolverResult = Result.SAT;
                        ReceivedResult = true;
                        break;
                    case "unsat":
                        SolverResult = Result.UNSAT;
                        ReceivedResult = true;
                        break;
                    case "unknown":
                        SolverResult = Result.UNKNOWN;
                        ReceivedResult = true;
                        ++InternalStatistics.SolverRepliedUnknownCount;
                        break;
                    default:
                        SolverResult = Result.UNKNOWN;
                        Console.Error.WriteLine("ERROR: Solver output \"" + stdoutLine.Data + "\" not parsed correctly");
                        SolverErrorMsg = SolverErrorMsg + stdoutLine.Data;
                        ReceivedError = true;
                        if (!PersistentProcess)
                            return;


                        break;
                }

                if (PersistentProcess)
                {
                    ReceivedResultEvent.Signal();
                }
                else
                {
                    Printer.PrintExit();
                }

            }

            protected virtual void ErrorHandler(object sendingProcess, DataReceivedEventArgs  stderrLine)
            {
                if (!String.IsNullOrEmpty(stderrLine.Data))
                {
                    Console.Error.WriteLine("Solver error received:");
                    Console.Error.WriteLine(stderrLine.Data);
                    ReceivedError = true;

                    if (PersistentProcess)
                        ReceivedResultEvent.Signal();
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

        public class SolverErrorException : Exception
        {
            public SolverErrorException(string msg) : base(msg)
            {

            }
        }

        public struct SimpleSMTLIBSolverStatistics : ISolverImplStatistics
        {
            public TimeSpan SolverProcessTime;
            public TimeSpan ReadExprTime;
            public TimeSpan PrintExprTime;
            public int ProcessCreationCount;
            public int TimeoutCount;
            public int SolverRepliedUnknownCount;

            public void Reset()
            {
                SolverProcessTime = TimeSpan.Zero;
                ReadExprTime = TimeSpan.Zero;
                PrintExprTime = TimeSpan.Zero;
                TimeoutCount = 0;
            }

            public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
            {
                TW.WriteLine("{0}:", this.GetType().ToString());
                TW.Indent += 1;
                TW.WriteLine("solver_process_time: {0}", SolverProcessTime.TotalSeconds);
                TW.WriteLine("read_expr_time: {0}", ReadExprTime.TotalSeconds);
                TW.WriteLine("print_expr_time: {0}", PrintExprTime.TotalSeconds);
                TW.WriteLine("process_create_count: {0}", ProcessCreationCount);
                TW.WriteLine("timeout_count: {0}", TimeoutCount);
                TW.WriteLine("solver_replied_unknown_count: {0}", SolverRepliedUnknownCount);
                TW.Indent -= 1;
            }

            public override string ToString()
            {
                string result;
                using (var SW = new StringWriter())
                {
                    using (var ITW = new System.CodeDom.Compiler.IndentedTextWriter(SW))
                    {
                        WriteAsYAML(ITW);
                    }
                    result = SW.ToString();
                }

                return result;
            }
        }
    }
}

