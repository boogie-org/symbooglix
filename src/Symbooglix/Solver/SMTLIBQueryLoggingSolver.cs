using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using Symbooglix;
using System.IO;


namespace Symbooglix
{
    namespace Solver
    {
        // SMTLIBQueryLoggingSolver and SMTLIBQueryLoggingSolverImpl
        // share quite a bit of code because they used to be the same
        // class which ended up being quite messy so they were separated

        public class SMTLIBQueryLoggingSolverImpl : ISolverImpl
        {
            private ISolverImpl UnderlyingImpl;
            private SMTLIBQueryPrinter Printer;
            private ConstraintManager CurrentConstraints = null;
            private int UseCounter=0;
            public SMTLIBQueryLoggingSolverImpl(ISolverImpl underlyingImplementation, TextWriter TW, bool humanReadable)
            {
                this.UnderlyingImpl = underlyingImplementation;
                Printer = new SMTLIBQueryPrinter(TW, humanReadable);
            }

            public void SetConstraints(ConstraintManager constraints)
            {
                // Let the printer find the declarations
                CurrentConstraints = constraints;
                foreach (var constraint in constraints.ConstraintExprs)
                {
                    Printer.AddDeclarations(constraint);
                }
                UnderlyingImpl.SetConstraints(constraints);
            }

            private void PrintDeclarationsAndConstraints()
            {
                Printer.PrintVariableDeclarations();
                Printer.PrintFunctionDeclarations();
                Printer.PrintCommentLine(CurrentConstraints.Count.ToString() +  " Constraints");
                foreach (var constraint in CurrentConstraints.Constraints)
                {
                    Printer.PrintCommentLine("Origin : " + constraint.Origin.ToString());
                    Printer.PrintAssert(constraint.Condition);
                }
            }

            public Tuple<Result, IAssignment> ComputeSatisfiability(Expr queryExpr, bool computeAssignment)
            {
                Printer.AddDeclarations(queryExpr);
                Printer.PrintCommentLine("Query " + UseCounter + " Begin");
                PrintDeclarationsAndConstraints();
                Printer.PrintCommentLine("Query Expr");
                Printer.PrintAssert(queryExpr);
                Printer.PrintCheckSat();

                var result = UnderlyingImpl.ComputeSatisfiability(queryExpr, computeAssignment);

                Printer.PrintCommentLine("Result : " + result.Item1);

                if (computeAssignment)
                {
                    // FIXME: Support this for query logging
                    Printer.PrintCommentLine(" WARNING: computeAssignment requested, but the printer doesn't support this!");
                }

                Printer.PrintExit();
                Printer.ClearDeclarations();
                Printer.PrintCommentLine("End of Query " + (UseCounter));
                ++UseCounter;
                return result;
            }

            public void SetTimeout(int seconds)
            {
                UnderlyingImpl.SetTimeout(seconds);
            }

            public void Dispose()
            {
                UnderlyingImpl.Dispose();
            }

            public ISolverImplStatistics GetStatistics()
            {
                return UnderlyingImpl.GetStatistics();
            }
        }
    }
}

