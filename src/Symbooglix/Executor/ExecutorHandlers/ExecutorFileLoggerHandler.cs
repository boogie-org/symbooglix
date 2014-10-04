﻿using System;
using System.IO;
using System.Collections.Generic;

namespace Symbooglix
{
    public class CouldNotCreateDirectoryException : Exception
    {
        public CouldNotCreateDirectoryException(string msg) : base(msg)
        {

        }
    }

    public class ExecutorFileLoggerHandler : IExecutorEventHandler
    {
        public DirectoryInfo RootDir
        {
            get;
            private set;
        }

        public DirectoryInfo TerminatedExecutionStatesDir
        {
            get;
            protected set;
        }

        private List<IExecutorEventHandler> Loggers;

        public ExecutorFileLoggerHandler(string path, bool makeDirectoryInPath)
        {
            this.RootDir = null;
            this.Loggers = new List<IExecutorEventHandler>();

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
                        this.RootDir = Directory.CreateDirectory(pathToUse);
                        break;
                    }
                    catch (Exception e)
                    {
                        throw new CouldNotCreateDirectoryException("Exception throw when creating: " + e.ToString());
                    }
                }

                if (this.RootDir == null)
                    throw new CouldNotCreateDirectoryException("Available numbers exhausted");

            }
            else
            {
                if (Directory.Exists(path))
                    throw new CouldNotCreateDirectoryException("Directory \"" + path + "\" already exists");

                // Just use the path
                try
                {
                    this.RootDir = Directory.CreateDirectory(path);
                }
                catch (Exception e)
                {
                    throw new CouldNotCreateDirectoryException("Exception throw when creating: " + e.ToString());
                }
            }

            CreateDirectories();
            SetupLoggers();
        }

        protected virtual void CreateDirectories()
        {
            TerminatedExecutionStatesDir = Directory.CreateDirectory(Path.Combine(this.RootDir.FullName, "terminated_states"));
        }

        protected virtual void SetupLoggers()
        {
            Loggers.Add(new ExecutionStateConstraintLogger(this.TerminatedExecutionStatesDir.FullName));
            Loggers.Add(new ExecutionStateUnSatCoreLogger(this.TerminatedExecutionStatesDir.FullName));
            Loggers.Add(new ExecutionStateInfoLogger(this.TerminatedExecutionStatesDir.FullName));
            Loggers.Add(new MemoryUsageLogger(this.RootDir.FullName));
        }

        public void Connect(Executor e)
        {
            foreach (var logger in Loggers)
                logger.Connect(e);
        }

        public void Disconnect(Executor e)
        {
            foreach (var logger in Loggers)
                logger.Disconnect(e);
        }
    }
}

