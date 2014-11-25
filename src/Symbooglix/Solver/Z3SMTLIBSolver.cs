using System;
using Symbooglix.Solver;

namespace Symbooglix
{
    namespace Solver
    {
        public class Z3SMTLIBSolver : SimpleSMTLIBSolver
        {
            private SMTLIBQueryPrinter.Logic LogicToUse = SMTLIBQueryPrinter.Logic.DO_NOT_SET;
            public Z3SMTLIBSolver(bool useNamedAttributes, string pathToSolver) : base(useNamedAttributes, pathToSolver, "-in -smt2") // Z3 specific command line args
            {
            }

            // HACK:
            public Z3SMTLIBSolver(bool useNamedAttributes, string pathToSolver, SMTLIBQueryPrinter.Logic logic) : this(useNamedAttributes, pathToSolver)
            {
                LogicToUse = logic;
            }

            protected override void SetSolverOptions()
            {
                Printer.PrintSetLogic(LogicToUse);
            }
        }
    }
}

