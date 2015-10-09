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
using System.Diagnostics;

namespace Symbooglix
{
    public class ExecutionStateConstraintLogger : ExecutionStateLogger
    {
        public ExecutionStateConstraintLogger(ExecutionStateLogger.ExecutorEventType eventToLog,
                                              Predicate<ExecutionState> toIgnoreFilter=null, bool logConcurrently=true) : base(eventToLog, toIgnoreFilter, logConcurrently) {}

        protected override void DoTask(Executor e, ExecutionState State)
        {
            string terminatationTypeName = null;

            if (State.TerminationType == null)
                terminatationTypeName = "NonTerminated";
            else
                terminatationTypeName = State.TerminationType.GetType().ToString();

            var path = Path.Combine(Directory, ((State.Id >= 0)?State.Id.ToString():"initial") + "-" + terminatationTypeName + ".smt2");

            using (var SW = new StreamWriter(path))
            {
                Console.WriteLine("Logging State {0} constraints to {1}", State.Id, path);
                var outputFile = new SMTLIBQueryPrinter(SW, true, true);

                outputFile.AnnotateAssertsWithNames = false; // Enabling this is really only useful for getting the unsat-core

                // FIXME: This **all** needs to be refactored. The solvers do something very similar
                foreach (var constraint in State.Constraints.Constraints)
                {
                    outputFile.AddDeclarations(constraint);
                }

                // Add declarations for any variables in the condition for sat if its available
                if (State.TerminationType is TerminationTypeWithSatAndUnsatExpr)
                {
                    var terminationType = State.TerminationType as TerminationTypeWithSatAndUnsatExpr;
                    Debug.Assert(terminationType.ConditionForSat != null, "ConditionForSat should not be null");
                    outputFile.AddDeclarations(terminationType.ConditionForSat);
                }

                outputFile.PrintSetOption("produce-models", "true");

                if (State.TerminationType == null)
                    outputFile.PrintCommentLine("Non terminated state");
                else
                    outputFile.PrintCommentLine(State.TerminationType.GetMessage());

                outputFile.PrintSortDeclarations();
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

