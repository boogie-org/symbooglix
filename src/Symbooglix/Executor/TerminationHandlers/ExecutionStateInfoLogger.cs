using System;
using System.IO;

namespace Symbooglix
{
    public class ExecutionStateInfoLogger : ExecutionStateLogger
    {
        protected override void DoTask(Executor e, ExecutionState State)
        {
            string terminatationTypeName = State.TerminationType.GetType().ToString();
            using (var SW = new StreamWriter(Path.Combine(Directory, State.Id + "-" + terminatationTypeName + ".txt")))
            {
                State.DumpState(SW,/*showConstraints=*/true, 4);
            }
        }
    }
}

