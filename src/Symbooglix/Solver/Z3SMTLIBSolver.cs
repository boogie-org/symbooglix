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
using Symbooglix.Solver;

namespace Symbooglix
{
    namespace Solver
    {
        public class Z3SMTLIBSolver : SimpleSMTLIBSolver
        {
            private SMTLIBQueryPrinter.Logic LogicToUse = SMTLIBQueryPrinter.Logic.DO_NOT_SET;
            public Z3SMTLIBSolver(bool useNamedAttributes, string pathToSolver, bool persistentProcess, bool emitTriggers) :
                base(useNamedAttributes, pathToSolver, "-in -smt2", persistentProcess, emitTriggers) // Z3 specific command line args
            {
                // HACK:
                // Z3 supports SMTLIB-v2.5 command (reset)
                if (persistentProcess)
                    this.UseReset = true;
            }

            // HACK:
            public Z3SMTLIBSolver(bool useNamedAttributes, string pathToSolver, bool persistentProcess, bool emitTriggers, SMTLIBQueryPrinter.Logic logic) :
                this(useNamedAttributes, pathToSolver, persistentProcess, emitTriggers)
            {
                LogicToUse = logic;
            }

            protected override void SetSolverOptions()
            {
                Printer.PrintSetLogic(LogicToUse);

                if (PersistentProcess)
                {
                    // Z3 4.3.1 by default has declarations be global by default
                    // which is not SMT-LIBv2 conformant. In order to implement the persistentProcess
                    // we need declarations to be part of the push-pop stack. Setting the option
                    // below gives the behaviour we want
                    Printer.PrintSetOption("global-decls", "false");
                }
            }
        }
    }
}

