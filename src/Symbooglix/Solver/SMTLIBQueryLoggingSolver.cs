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
                    Printer.addDeclarations(constraint);
                }
                UnderlyingSolver.SetConstraints(cm);
            }

            public void SetTimeout(int seconds)
            {
                UnderlyingSolver.SetTimeout(seconds);
            }

            private void PrintDeclarationsAndConstraints()
            {
                Printer.printVariableDeclarations();
                Printer.printFunctionDeclarations();
                Printer.printCommentLine(CurrentConstraints.Constraints.Count.ToString() +  " Constraints");
                foreach (var constraint in CurrentConstraints.Constraints)
                {
                    Printer.printAssert(constraint);
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
                Printer.addDeclarations(QueryToPrint);
                Printer.printCommentLine("Query " + UseCounter + " Begin");
                PrintDeclarationsAndConstraints();
                Printer.printCommentLine(commentLine);
                Printer.printAssert(QueryToPrint);
                Printer.printCheckSat();
                Result result = handler(QueryToUnderlyingSolver);
                Printer.printCommentLine("Result : " + result);
                Printer.printExit();
                Printer.clearDeclarations();
                Printer.printCommentLine("End of Query " + (UseCounter));
                ++UseCounter;
                return result;
            }

        }
    }
}

