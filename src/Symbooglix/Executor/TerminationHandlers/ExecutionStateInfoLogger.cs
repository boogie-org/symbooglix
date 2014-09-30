using System;
using System.Threading.Tasks;
using System.Threading;
using System.Collections.Generic;
using System.IO;

namespace Symbooglix
{
    public abstract class ExecutionStateInfoLogger : IExecutorEventHandler
    {
        protected string Directory;
        public ExecutionStateInfoLogger(string directory)
        {
            this.Directory = directory;
        }

        private List<Task> ScheduledTasks = new List<Task>();

        private void handle(Object executor, Executor.ExecutionStateEventArgs args)
        {
            lock (ScheduledTasks)
            {
                var task = Task.Factory.StartNew(() =>
                {
                    DoTask(executor as Executor, args.State);
                });
                ScheduledTasks.Add(task);
            }
        }

        public void Connect(Executor e)
        {
            e.StateTerminated += handle;
        }

        public void Disconnect(Executor e)
        {
            e.StateTerminated -= handle;
        }

        protected abstract void DoTask(Executor e, ExecutionState State);

        // Yuck! Is there a better way to do this that ensures that our Tasks
        // always finish before the program is allowed to Terminate?
        public void Wait()
        {
            Task.WaitAll(ScheduledTasks.ToArray());
        }
    }

    public class ExecutionStateConstraintLogger : ExecutionStateInfoLogger
    {
        public ExecutionStateConstraintLogger(string directory) : base(directory)
        {
        }

        protected override void DoTask(Executor e, ExecutionState State)
        {
            string terminatationTypeName = State.TerminationType.GetType().ToString();
            using (var SW = new StreamWriter(Path.Combine(Directory,State.Id + "-" + terminatationTypeName + ".smt2")))
            {
                var outputFile = new SMTLIBQueryPrinter(SW, true);

                outputFile.AnnotateAssertsWithNames = false; // Enabling this is really only useful for getting the unsat-core

                // FIXME: This **all** needs to be refactored. The solvers do something very similar
                foreach (var constraint in State.Constraints.ConstraintExprs)
                {
                    outputFile.AddDeclarations(constraint);
                }

                // Add declarations for any variables in the condition for sat if its available
                if (State.TerminationType is TerminationTypeWithSatAndUnsatExpr)
                {
                    var terminationType = State.TerminationType as TerminationTypeWithSatAndUnsatExpr;
                    outputFile.AddDeclarations(terminationType.ConditionForSat);
                }

                outputFile.PrintSetOption("produce-models", "true");
                outputFile.PrintCommentLine(State.TerminationType.GetMessage());
                outputFile.PrintFunctionDeclarations();
                outputFile.PrintVariableDeclarations();

                foreach (var constraint in State.Constraints.Constraints)
                {
                    outputFile.PrintCommentLine("Origin : " + constraint.Origin.ToString());
                    outputFile.PrintAssert(constraint.Condition);
                }

                // This adds the last constraint if there is one
                if (State.TerminationType is TerminationTypeWithSatAndUnsatExpr)
                {
                    var terminationType = State.TerminationType as TerminationTypeWithSatAndUnsatExpr;
                    outputFile.PrintCommentLine("Query Expr:SAT");
                    outputFile.PrintAssert(terminationType.ConditionForSat);
                }

                outputFile.PrintCheckSat();
                outputFile.PrintGetModel();
                outputFile.PrintExit();
            }
        }
    }

    public class ExecutionStateUnSatCoreLogger : ExecutionStateInfoLogger
    {
        public ExecutionStateUnSatCoreLogger(string directory) : base(directory)
        {
        }

        protected override void DoTask(Executor e, ExecutionState State)
        {
            string terminatationTypeName = State.TerminationType.GetType().ToString();

            if (!(State.TerminationType is TerminationTypeWithSatAndUnsatExpr))
                return;

            var terminationType = State.TerminationType as TerminationTypeWithSatAndUnsatExpr;

            if (terminationType.ConditionForUnsat == null)
                return;

            using (var SW = new StreamWriter(Path.Combine(Directory,State.Id + "-" + terminatationTypeName + ".unsatcore.smt2")))
            {
                var outputFile = new SMTLIBQueryPrinter(SW, true);

                outputFile.AnnotateAssertsWithNames = true; // Needed for unsat-core

                // FIXME: This **all** needs to be refactored. The solvers do something very similar
                foreach (var constraint in State.Constraints.ConstraintExprs)
                {
                    outputFile.AddDeclarations(constraint);
                }

                outputFile.AddDeclarations(terminationType.ConditionForSat);

                outputFile.PrintSetOption("produce-unsat-cores", "true");
                outputFile.PrintCommentLine(State.TerminationType.GetMessage());
                outputFile.PrintFunctionDeclarations();
                outputFile.PrintVariableDeclarations();

                foreach (var constraint in State.Constraints.Constraints)
                {
                    outputFile.PrintCommentLine("Origin : " + constraint.Origin.ToString());
                    outputFile.PrintAssert(constraint.Condition);
                }


                outputFile.PrintCommentLine("Query Expr:UNSAT");
                outputFile.PrintAssert(terminationType.ConditionForUnsat);


                outputFile.PrintCheckSat();
                outputFile.PrintGetUnsatCore();
                outputFile.PrintExit();
            }
        }
    }
}

