using System;
using System.IO;

namespace Symbooglix
{
    public class ExecutionStateUnSatCoreLogger : ExecutionStateLogger
    {
        public ExecutionStateUnSatCoreLogger(ExecutionStateLogger.ExecutorEventType eventToLog) : base(eventToLog) { }

        protected override void DoTask(Executor e, ExecutionState State)
        {
            string terminatationTypeName = State.TerminationType.GetType().ToString();

            if (!(State.TerminationType is TerminationTypeWithSatAndUnsatExpr))
                return;

            var terminationType = State.TerminationType as TerminationTypeWithSatAndUnsatExpr;

            if (terminationType.ConditionForUnsat == null)
                return;

            var path = Path.Combine(Directory, State.Id + "-" + terminatationTypeName + ".unsatcore.smt2");
            using (var SW = new StreamWriter(path))
            {
                Console.WriteLine("Logging State {0} unsat core constraints to {1}", State.Id, path);
                var outputFile = new SMTLIBQueryPrinter(SW, true, true);

                outputFile.AnnotateAssertsWithNames = true; // Needed for unsat-core

                // FIXME: This **all** needs to be refactored. The solvers do something very similar
                foreach (var constraint in State.Constraints.ConstraintExprs)
                {
                    outputFile.AddDeclarations(constraint);
                }

                outputFile.AddDeclarations(terminationType.ConditionForUnsat);

                outputFile.PrintSetOption("produce-unsat-cores", "true");

                if (State.TerminationType == null)
                    outputFile.PrintCommentLine("Non terminated state");
                else
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

