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
        }

        public void Connect(Executor e)
        {
            TerminatedStateConstraintsLogger.Connect(e);
        }

        public void Disconnect(Executor e)
        {
            TerminatedStateConstraintsLogger.Disconnect(e);
        }

        public void Wait()
        {
            // FIXME: Add a finished event to Executor so the Wait() can be triggered automatically.
            TerminatedStateConstraintsLogger.Wait();
        }
    }
}

