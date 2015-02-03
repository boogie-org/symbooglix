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
            protected IConstraintManager CurrentConstraints = null;
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

            // FIXME: This API sucks sooo much
            // Only has meaning if PersistentProcess is True
            protected bool UseReset;

            protected SimpleSMTLIBSolver(bool useNamedAttributes, string PathToSolverExecutable, string solverArguments, bool persistentProcess)
            {
                if (! File.Exists(PathToSolverExecutable))
                    throw new SolverNotFoundException(PathToSolverExecutable);

                SolverOptionsSet = false;
                ReceivedError = false;
                ReceivedResultEvent = null;
                this.PersistentProcess = persistentProcess;
                UseReset = false;

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

                    this.TheProcess = Process.Start(StartInfo);

                    if (Printer == null)
                        Printer = new SMTLIBQueryPrinter(GetStdInput(), /*useNamedAttributeBindings*/UseNamedAttributes, /*humanReadable=*/false);
                    else
                        Printer.ChangeOutput(GetStdInput());


                    // Register for asynchronous callbacks
                    TheProcess.OutputDataReceived += OutputHandler;
                    TheProcess.ErrorDataReceived += ErrorHandler;
                    TheProcess.BeginOutputReadLine();
                    TheProcess.BeginErrorReadLine();
                    SolverOptionsSet = false;
                    SolverProcessTimer.Stop();
                }
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

            public void SetConstraints(IConstraintManager cm)
            {
                ReadExprTimer.Start();
                Printer.ClearDeclarations();

                // Let the printer find the declarations
                CurrentConstraints = cm;
                foreach (var constraint in cm.Constraints)
                {
                    Printer.AddDeclarations(constraint);
                }
                ReadExprTimer.Stop();
            }

            public void SetTimeout(int seconds)
            {
                if (seconds < 0)
                    throw new InvalidSolverTimeoutException();

                Timeout = seconds;
            }

            private void PrintDeclarationsAndConstraints()
            {
                Printer.PrintSortDeclarations();
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
            public Tuple<Result, IAssignment> ComputeSatisfiability(Expr queryExpr, bool computeAssignment)
            {
                lock (ComputeSatisfiabilityLock)
                {
                    Interrupted = false;
                    ReceivedResult = false;
                    ReceivedError = false;
                    SolverResult = Result.UNKNOWN;

                    if (computeAssignment)
                        throw new NotSupportedException("Can't handle assignments yet");

                    // FIXME: This is only needed for PersistentProcess mode but we need
                    // to initialise it before we could get a response from the solver other we might race.
                    // In fact there still might be a race here...
                    using (ReceivedResultEvent = new CountdownEvent(1))
                    {
                        ReadExprTimer.Start();
                        Printer.AddDeclarations(queryExpr);
                        ReadExprTimer.Stop();

                        // Assume the process has already been setup
                        try
                        {
                            PrintExprTimer.Start();

                            // Set options if the current process hasn't been given them before or if we're using (reset)
                            if (!SolverOptionsSet || UseReset)
                            {
                                SetSolverOptions();
                                SolverOptionsSet = true;
                            }

                            if (PersistentProcess && !UseReset)
                                Printer.PrintPushDeclStack(1);

                            PrintDeclarationsAndConstraints();
                            Printer.PrintAssert(queryExpr);

                            // Start the timer for the process now. The solver should start processing as soon as we write (check-sat)
                            SolverProcessTimer.Start();

                            Printer.PrintCheckSat();
                            PrintExprTimer.Stop();
                        }
                        catch (System.IO.IOException)
                        {
                            // This might happen if the process gets killed whilst we are trying to write
                            if (!ReceivedResult)
                            {
                                Console.Error.WriteLine("Failed to get solver result!");
                                SolverResult = Result.UNKNOWN;
                                return Tuple.Create(SolverResult, null as IAssignment);
                            }
                        }
                        catch (ObjectDisposedException)
                        {
                            Console.Error.WriteLine("Warning hit ObjectDisposedException. Assuming we are being disposed of!");
                            // Race condition, We got killed while trying to print. Just give up!
                            SolverResult = Result.UNKNOWN;
                            return Tuple.Create(SolverResult, null as IAssignment);
                        }
                        catch (UnauthorizedAccessException)
                        {
                            Console.Error.WriteLine("Warning hit UnauthorizedAccessException. Just returning unknown");
                            SolverResult = Result.UNKNOWN;
                            return Tuple.Create(SolverResult, null as IAssignment);
                        }

                        // Handle result
                        if (PersistentProcess)
                        {
                            // In persistent mode try to avoid killing the solver process so have to use
                            // a different synchronisation method to check if we've received a result

                            // Wait for result
                            if (Timeout > 0)
                                ReceivedResultEvent.Wait(Timeout * 1000);
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

                            if (!ReceivedResult || ReceivedError || processExited || ReceivedResultEvent.CurrentCount > 0)
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
                                TheProcess.WaitForExit(Timeout * 1000);
                            else
                                TheProcess.WaitForExit();

                            if (!ReceivedResult)
                            {
                                Console.Error.WriteLine("Failed to get solver result!");
                                SolverResult = Result.UNKNOWN;
                            }

                            if (SolverProcessTimer.IsRunning)
                                SolverProcessTimer.Stop();

                            CreateNewProcess(); // For next invocation
                        }
                    }
                    ReceivedResultEvent = null;

                    return Tuple.Create(SolverResult, null as IAssignment);
                }
            }

            protected virtual void OutputHandler(object sendingProcess, DataReceivedEventArgs stdoutLine)
            {
                // The event handler might get called more than once.
                // In fact for Z3 we get called twice, first with the result
                // and then again with a blank line (why?)
                if (String.IsNullOrEmpty(stdoutLine.Data) || ReceivedResult)
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

        public struct SimpleSMTLIBSolverStatistics : ISolverImplStatistics
        {
            public TimeSpan SolverProcessTime;
            public TimeSpan ReadExprTime;
            public TimeSpan PrintExprTime;
            public int ProcessCreationCount;

            public void Reset()
            {
                SolverProcessTime = TimeSpan.Zero;
                ReadExprTime = TimeSpan.Zero;
                PrintExprTime = TimeSpan.Zero;
            }

            public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
            {
                TW.WriteLine("{0}:", this.GetType().ToString());
                TW.Indent += 1;
                TW.WriteLine("solver_process_time: {0}", SolverProcessTime.TotalSeconds);
                TW.WriteLine("read_expr_time: {0}", ReadExprTime.TotalSeconds);
                TW.WriteLine("print_expr_time: {0}", PrintExprTime.TotalSeconds);
                TW.WriteLine("process_create_count: {0}", ProcessCreationCount);
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

