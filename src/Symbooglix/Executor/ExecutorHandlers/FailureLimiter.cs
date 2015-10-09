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

namespace Symbooglix
{
    public class FailureLimiter : TerminationCounter
    {
        public int FailureLimit
        {
            get;
            private set;
        }
        public FailureLimiter(int failureLimit)
        {
            if (failureLimit < 1)
                throw new ArgumentException("failureLimit must be >= 1");

            FailureLimit = failureLimit;
        }

        public override void Connect(Executor e)
        {
            e.StateTerminated += HandleStateTerminated;
        }

        void HandleStateTerminated(object sender, Executor.ExecutionStateEventArgs e)
        {
            // Make sure the counting happens first
            base.handle(sender, e);

            if (NumberOfFailures >= FailureLimit)
            {
                var executor = sender as Executor;
                Console.WriteLine("Failure limit of {0} reached. Terminating Executor", FailureLimit);
                // Don't interrupt the solver, this can lead to non-deterministic behaviour
                executor.Terminate(/*block=*/ false, /*interruptSolver=*/ false);
            }
        }

        public override void Disconnect(Executor e)
        {
            e.StateTerminated -= HandleStateTerminated;
        }
    }
}

