using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.IO;

namespace Symbooglix
{
    namespace Solver
    {
        // FIXME: We need to refactor this so it can reused to builder an actual solver
        public class SMTLIBQueryLoggingSolver : ISolver
        {
            private ISolver UnderlyingSolver;
            private SMTLIBQueryPrinter Printer;
            private int UseCounter=0;
            private ConstraintManager CurrentConstraints = null;
            public SMTLIBQueryLoggingSolver(ISolver UnderlyingSolver, TextWriter TW, bool humanReadable)
            {
                this.UnderlyingSolver = UnderlyingSolver;
                Printer = new SMTLIBQueryPrinter(TW, humanReadable);
            }

            public void SetConstraints(ConstraintManager cm)
            {
                // Let the printer find the declarations
                CurrentConstraints = cm;
                foreach (var constraint in cm.Constraints)
                {
                    Printer.AddDeclarations(constraint);
                }
                UnderlyingSolver.SetConstraints(cm);
            }

            public void SetTimeout(int seconds)
            {
                UnderlyingSolver.SetTimeout(seconds);
            }

            private void PrintDeclarationsAndConstraints()
            {
                Printer.PrintVariableDeclarations();
                Printer.PrintFunctionDeclarations();
                Printer.PrintCommentLine(CurrentConstraints.Constraints.Count.ToString() +  " Constraints");
                foreach (var constraint in CurrentConstraints.Constraints)
                {
                    Printer.PrintAssert(constraint);
                }
            }

            public Result IsQuerySat(Expr Query, out IAssignment assignment)
            {
                throw new NotImplementedException();
            }

            public Result IsQuerySat(Expr Query)
            {
                return DoQuery(Query, Query, UnderlyingSolver.IsQuerySat, "IsQuerySat");
            }

            public Result IsNotQuerySat(Expr Query, out IAssignment assignment)
            {
                throw new NotImplementedException();
            }

            public Result IsNotQuerySat(Expr Query)
            {
                // At every layer we'll be creating a NotExpr, this isn't great, perhaps we should
                // forward to a SolverImpl class that only supports isQuerySat and only create the NotExpr
                // at the first layer?
                return DoQuery(Expr.Not(Query), Query, UnderlyingSolver.IsNotQuerySat, "IsNotQuerySat");
            }

            private delegate Result QueryOperation(Expr Query);
            private Result DoQuery(Expr QueryToPrint, Expr QueryToUnderlyingSolver, QueryOperation handler, string commentLine)
            {
                Printer.AddDeclarations(QueryToPrint);
                Printer.PrintCommentLine("Query " + UseCounter + " Begin");
                PrintDeclarationsAndConstraints();
                Printer.PrintCommentLine(commentLine);
                Printer.PrintAssert(QueryToPrint);
                Printer.PrintCheckSat();
                Result result = handler(QueryToUnderlyingSolver);
                Printer.PrintCommentLine("Result : " + result);
                Printer.PrintExit();
                Printer.ClearDeclarations();
                Printer.PrintCommentLine("End of Query " + (UseCounter));
                ++UseCounter;
                return result;
            }

        }
    }
}

