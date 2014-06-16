using System;
using System.Diagnostics;
using System.IO;
using Microsoft.Boogie;

namespace symbooglix
{
    namespace Solver
    {
        // FIXME: Refactor this and SMTLIBQueryLoggingSolver
        public class SimpleSMTLIBSolver : ISolver
        {
            public int Timeout { get; private set;}
            private SMTLIBQueryPrinter Printer = null;
            private ConstraintManager currentConstraints = null;
            private ProcessStartInfo startInfo;
            public SimpleSMTLIBSolver(string PathToSolverExecutable)
            {
                if (! File.Exists(PathToSolverExecutable))
                    throw new SolverNotFoundException(PathToSolverExecutable);

                startInfo = new ProcessStartInfo(PathToSolverExecutable, "-in -smt2"); // FIXME: This is Z3 specific
                startInfo.RedirectStandardInput = true; // Neccessary so we can send our query
                startInfo.RedirectStandardOutput = true; // Necessary so we can read the output
                startInfo.UseShellExecute = false; // C# docs say this is required

                //Printer = new SMTLIBQueryPrinter(TW, /*humanReadable=*/ false);
            }

            public void SetConstraints(ConstraintManager cm)
            {
                Printer.clearDeclarations();

                // Let the printer find the declarations
                currentConstraints = cm;
                foreach (var constraint in cm.constraints)
                {
                    Printer.addDeclarations(constraint);
                }
            }

            public void SetTimeout(int seconds)
            {
                if (seconds < 0)
                    throw new InvalidSolverTimeoutException();

                Timeout = seconds;
            }

            private void printDeclarationsAndConstraints()
            {
                Printer.printVariableDeclarations();
                Printer.printFunctionDeclarations();
                Printer.printCommentLine(currentConstraints.constraints.Count.ToString() +  " Constraints");
                foreach (var constraint in currentConstraints.constraints)
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
                return doQuery(Query);
            }

            public Result IsNotQuerySat(Expr Query, out IAssignment assignment)
            {
                throw new NotImplementedException();
            }

            public Result IsNotQuerySat(Expr Query)
            {
                return doQuery(Expr.Not(Query));
            }

            private Result doQuery(Expr QueryToPrint)
            {
                Result result = Result.UNKNOWN;
                Printer.addDeclarations(QueryToPrint);

                // Create Process
                var proc = Process.Start(startInfo);

                if (Printer == null)
                {
                    Printer = new SMTLIBQueryPrinter(proc.StandardInput, /*humanReadable=*/false);
                }
                else
                {
                    Printer.changeOutput(proc.StandardInput);
                }

                printDeclarationsAndConstraints();
                Printer.printAssert(QueryToPrint);
                Printer.printCheckSat();

                // TODO: Register delegates to receive solver response

                proc.WaitForExit(Timeout * 1000);

                // TODO: Check we got the response we wanted

                Printer.printExit();
                Printer.clearDeclarations();
                return result;
            }
        }

        public class SolverNotFoundException : Exception
        {
            public SolverNotFoundException(string path) : base("The Solver \"" + path + "\" could not be found")
            {

            }
        }
    }
}

