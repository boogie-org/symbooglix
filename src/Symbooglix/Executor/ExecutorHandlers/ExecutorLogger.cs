using System;
using System.IO;

namespace Symbooglix
{
    public class CouldNotCreateDirectoryException : Exception
    {
        public CouldNotCreateDirectoryException(string msg) : base(msg)
        {

        }
    }

    public class ExecutorLogger : IExecutorEventHandler
    {
        public DirectoryInfo Root
        {
            get;
            private set;
        }

        public DirectoryInfo TerminatedExecutionStatesDir
        {
            get;
            private set;
        }

        private ExecutionStateInfoLogger TerminatedStateConstraintsLogger;
        private ExecutionStateInfoLogger TerminatedStateUnsatCoreLogger;

        public ExecutorLogger(string path, bool makeDirectoryInPath)
        {
            this.Root = null;

            if (makeDirectoryInPath)
            {
                // Try to find an available directory to log stuff in
                // FIXME: How do we fix the TOCTOU here?
                for (int counter = 0; counter < 5000; ++counter)
                {
                    string pathToUse = Path.Combine(path, "symbooglix-" + counter);

                    if (Directory.Exists(pathToUse))
                        continue;

                    try
                    {
                        this.Root = Directory.CreateDirectory(pathToUse);
                        break;
                    }
                    catch (Exception e)
                    {
                        throw new CouldNotCreateDirectoryException("Exception throw when creating: " + e.ToString());
                    }
                }

                if (this.Root == null)
                    throw new CouldNotCreateDirectoryException("Available numbers exhausted");

            }
            else
            {
                if (Directory.Exists(path))
                    throw new CouldNotCreateDirectoryException("Directory \"" + path + "\" already exists");

                // Just use the path
                try
                {
                    this.Root = Directory.CreateDirectory(path);
                }
                catch (Exception e)
                {
                    throw new CouldNotCreateDirectoryException("Exception throw when creating: " + e.ToString());
                }
            }

            SetupLoggers();
        }

        private void CreateDirectories()
        {
            TerminatedExecutionStatesDir = Directory.CreateDirectory(Path.Combine(this.Root.FullName, "terminated_states"));
        }

        protected virtual void SetupLoggers()
        {
            CreateDirectories();
            TerminatedStateConstraintsLogger = new ExecutionStateConstraintLogger(this.TerminatedExecutionStatesDir.FullName);
            TerminatedStateUnsatCoreLogger = new ExecutionStateUnSatCoreLogger(this.TerminatedExecutionStatesDir.FullName);
        }

        public void Connect(Executor e)
        {
            TerminatedStateConstraintsLogger.Connect(e);
            TerminatedStateUnsatCoreLogger.Connect(e);

            // This forces the Executor to block() whilst we wait for our logging to finish
            e.ExecutorTerminated += this.Wait;
        }

        public void Disconnect(Executor e)
        {
            TerminatedStateConstraintsLogger.Disconnect(e);
            TerminatedStateUnsatCoreLogger.Disconnect(e);
            e.ExecutorTerminated -= this.Wait;
        }

        private void Wait(Object executor, Executor.ExecutorTerminatedArgs args)
        {
            Console.WriteLine("Executor terminated. Waiting for logging to finish...");
            TerminatedStateConstraintsLogger.Wait();
            TerminatedStateUnsatCoreLogger.Wait();
            Console.WriteLine("Logging finished");
        }
    }
}

