using System;
using System.IO;

namespace Symbooglix
{
    public class ExecutionStateInfoLogger : ExecutionStateLogger
    {
        public ExecutionStateInfoLogger(ExecutionStateLogger.ExecutorEventType eventToLog) : base(eventToLog) { }

        protected override void DoTask(Executor e, ExecutionState State)
        {
            string terminatationTypeName = null;

            if (State.TerminationType == null)
                terminatationTypeName = "NonTerminated";
            else
                terminatationTypeName = State.TerminationType.GetType().ToString();

            using (var SW = new StreamWriter(Path.Combine(Directory, State.Id + "-" + terminatationTypeName + ".txt")))
            {
                State.DumpState(SW,/*showConstraints=*/true, 4);
            }
        }
    }
}

