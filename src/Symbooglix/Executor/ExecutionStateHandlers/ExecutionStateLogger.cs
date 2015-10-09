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
using System.Threading.Tasks;
using System.Threading;
using System.Collections.Generic;
using System.IO;

namespace Symbooglix
{
    public abstract class ExecutionStateLogger : AbstractExecutorFileLogger
    {
        public enum ExecutorEventType
        {
            TERMINATED_STATE,
            NON_TERMINATED_STATE_REMOVED,
        }
        ExecutorEventType EventToLog;
        private readonly bool UseTasks;
        protected Predicate<ExecutionState> ToIgnoreFilter; // Returns true iff the execution state should be ignored, null if no filter

        public ExecutionStateLogger(ExecutorEventType EventToLog, Predicate<ExecutionState> toIgnoreFilter, bool logConcurrently)
        {
            this.EventToLog = EventToLog;
            this.ToIgnoreFilter = toIgnoreFilter;
            this.UseTasks = logConcurrently;
        }

        private List<Task> ScheduledTasks = new List<Task>();

        private void DoLogging(Executor executor, ExecutionState state)
        {
            if (ToIgnoreFilter != null && ToIgnoreFilter(state))
            {
                return; // Don't log
            }
            DoTask(executor, state);
        }

        private void handle(Object executor, Executor.ExecutionStateEventArgs args)
        {
            if (UseTasks)
            {
                lock (ScheduledTasks)
                {
                    var task = Task.Factory.StartNew(() =>
                    {
                        DoLogging(executor as Executor, args.State);
                    });
                    ScheduledTasks.Add(task);
                }
            }
            else
            {
                DoLogging(executor as Executor, args.State);
            }
        }

        public override void Connect(Executor e)
        {
            switch (EventToLog)
            {
                case ExecutorEventType.TERMINATED_STATE:
                    e.StateTerminated += handle;
                    break;
                case ExecutorEventType.NON_TERMINATED_STATE_REMOVED:
                    e.NonTerminatedStateRemoved += handle;
                    break;
                default:
                    throw new ArgumentException("Unsupported CaptureType");
            }

            if (UseTasks)
                e.ExecutorTerminated += Wait;
        }

        public override void Disconnect(Executor e)
        {
            switch (EventToLog)
            {
                case ExecutorEventType.TERMINATED_STATE:
                    e.StateTerminated -= handle;
                    break;
                case ExecutorEventType.NON_TERMINATED_STATE_REMOVED:
                    e.NonTerminatedStateRemoved -= handle;
                    break;
                default:
                    throw new ArgumentException("Unsupported CaptureType");
            }

            if (UseTasks)
                e.ExecutorTerminated -= Wait;
        }

        protected abstract void DoTask(Executor e, ExecutionState State);

        // We need a way to ensure that our tasks finish before the application
        // using this class exits because it will just exit without letting our
        // tasks finish if we don't explicitly wait. This is achieved by hooking
        // into the ExecutorTerminated event and then waiting on all the tasks we
        // have. Is there a better way to do this???
        private void Wait(Object executor, Executor.ExecutorTerminatedArgs args)
        {
            lock (ScheduledTasks)
            {
                Task.WaitAll(ScheduledTasks.ToArray());
            }
        }
    }
}

