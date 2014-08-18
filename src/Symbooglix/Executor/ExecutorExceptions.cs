using System;

namespace Symbooglix
{
    public class ExecutorException : Exception
    {
        public Executor TheExecutor{ get; private set;}
        public ExecutorException(Executor executor, string msg) : base(msg)
        {
            TheExecutor = executor;
        }
    }

    public class ExecuteTerminatedStateException : ExecutorException
    {
        public ExecutionState State { get; private set; }

        public ExecuteTerminatedStateException(Executor executor, ExecutionState state) : base(executor, "Cannot execute terminated state")
        {
            this.State = state;
        }
    }
}

