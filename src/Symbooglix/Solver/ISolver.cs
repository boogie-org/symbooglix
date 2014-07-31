using System;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    namespace Solver
    {
        public enum Result {SAT, UNSAT, UNKNOWN};

        // This solver interface is what the Executor uses and thus
        // is designed around the needs of the Executor rather than the solver
        public interface ISolver : IDisposable
        {
            void SetConstraints(ConstraintManager cm);

            void SetTimeout(int seconds);

            // Given the constraints is the query expression satisfiable
            // \return True iff sat
            // if sat the assignment will be set to an assignment object
            //
            // If another query is made the previously received assignment object may be
            // invalid.
            Result IsQuerySat(Microsoft.Boogie.Expr query, out IAssignment assignment);

            // Same as above but no assignment is requested
            Result IsQuerySat(Microsoft.Boogie.Expr query);

            // Given the constraints is the negation of the query expression satisfiable
            // \return True iff sat
            // if sat the assignment will be set to an assignment object
            //
            // If another query is made the previously received assignment object may be
            // invalid.
            Result IsNotQuerySat(Microsoft.Boogie.Expr query, out IAssignment assignment);

            // Same as above but no assignment is requested
            Result IsNotQuerySat(Microsoft.Boogie.Expr query);

            // Get access to the underlying implementation
            ISolverImpl SolverImpl { get; }
        }

        public interface IAssignment
        {
            Microsoft.Boogie.LiteralExpr GetAssignment(SymbolicVariable SV);
        }

        public class InvalidSolverTimeoutException : Exception
        {

        }
    }
}

