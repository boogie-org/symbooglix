using System;
using System.IO;

namespace Symbooglix
{
    public class ExecutionStateConstraintLogger : ExecutionStateLogger
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

}

