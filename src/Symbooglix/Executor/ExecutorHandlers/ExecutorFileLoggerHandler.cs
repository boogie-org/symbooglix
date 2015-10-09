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

    public class ExecutorFileLoggerHandler
    {
        private Executor TheExecutor;
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

        public DirectoryInfo NonTerminatedExcecutionStatesDir
        {
            get;
            protected set;
        }

        private List<IExecutorEventHandler> Loggers;


        public ExecutorFileLoggerHandler(Executor executor, string path, bool makeDirectoryInPath)
        {
            this.TheExecutor = executor;
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
        }

        protected virtual void CreateDirectories()
        {
            TerminatedExecutionStatesDir = Directory.CreateDirectory(Path.Combine(this.RootDir.FullName, "terminated_states"));
            NonTerminatedExcecutionStatesDir = Directory.CreateDirectory(Path.Combine(this.RootDir.FullName, "nonterminated_states"));
        }

        public void AddTerminatedStateDirLogger(AbstractExecutorFileLogger logger)
        {
            logger.SetDirectory(this.TerminatedExecutionStatesDir.FullName);
            Loggers.Add(logger);
        }

        public void AddRootDirLogger(AbstractExecutorFileLogger logger)
        {
            logger.SetDirectory(this.RootDir.FullName);
            Loggers.Add(logger);
        }

        public void AddNonTerminatedStateDirLogger(AbstractExecutorFileLogger logger)
        {
            logger.SetDirectory(this.NonTerminatedExcecutionStatesDir.FullName);
            Loggers.Add(logger);
        }

        private bool Connected = false;
        public void Connect()
        {
            lock (Loggers)
            {
                if (Connected)
                    throw new InvalidOperationException("Can't connect loggers again");

                foreach (var logger in this.Loggers)
                    logger.Connect(TheExecutor);

                Connected = true;
            }
        }
    }
}

