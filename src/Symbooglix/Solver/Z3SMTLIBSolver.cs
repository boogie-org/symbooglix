using System;
using Symbooglix.Solver;

namespace Symbooglix
{
    namespace Solver
    {
        public class Z3SMTLIBSolver : SimpleSMTLIBSolver
        {
            public Z3SMTLIBSolver(string pathToSolver) : base(pathToSolver)
            {
                this.StartInfo.Arguments = "-in -smt2"; // Z3 specific command line flags
            }
        }
    }
}

