using System;
using System.Collections.Generic;

namespace symbooglix
{
    namespace Solver
    {
        public enum Result {SAT, UNSAT, UNKNOWN};

        public interface ISolver
        {
            void SetConstraints(ConstraintManager cm);

            void SetTimeout(int seconds);

            // Given the constraints is the query expression satisfiable
            // \return True iff sat
            // if sat the assignment will be set to an assignment object
            //
            // If another query is made the previously received assignment object may be
            // invalid.
            Result IsQuerySat(Microsoft.Boogie.Expr Query, out IAssignment assignment);

            // Same as above but no assignment is requested
            Result IsQuerySat(Microsoft.Boogie.Expr Query);

            // Given the constraints is the negation of the query expression satisfiable
            // \return True iff sat
            // if sat the assignment will be set to an assignment object
            //
            // If another query is made the previously received assignment object may be
            // invalid.
            Result IsNotQuerySat(Microsoft.Boogie.Expr Query, out IAssignment assignment);

            // Same as above but no assignment is requested
            Result IsNotQuerySat(Microsoft.Boogie.Expr Query);
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

