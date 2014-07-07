using System;
using Symbooglix.Solver;

namespace Symbooglix
{
    namespace Solver
    {
        public class CVC4SMTLIBSolver : SimpleSMTLIBSolver
        {
            public CVC4SMTLIBSolver(string pathToSolver) : base(pathToSolver)
            {
                this.StartInfo.Arguments = "--lang smt2"; // CVC4 specific command line flags
            }

            protected override void SetSolverOptions()
            {
                Printer.printSetLogic(SMTLIBQueryPrinter.Logic.ALL_SUPPORTED); // Non standard
            }
        }
    }
}

