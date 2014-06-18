using System;
using symbooglix.Solver;

namespace symbooglix
{
    namespace Solver
    {
        public class Z3SMTLIBSolver : SimpleSMTLIBSolver
        {
            public Z3SMTLIBSolver(string pathToSolver) : base(pathToSolver)
            {
                this.startInfo.Arguments = "-in -smt2"; // Z3 specific command line flags
            }
        }
    }
}

