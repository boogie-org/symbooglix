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
            void SetFunctions(IEnumerable<Microsoft.Boogie.Function> functions);


            // Given the constraints is the query expression satisfiable
            // \return True iff sat
            // if sat the assignment will be set to an assignment object
            //
            // If another query is made the previously received assignment object may be
            // invalid.
            Result IsQuerySat(Microsoft.Boogie.Expr Query, out IAssignment assignment);

            // Given the constraints is the negation of the query expression satisfiable
            // \return True iff sat
            // if sat the assignment will be set to an assignment object
            //
            // If another query is made the previously received assignment object may be
            // invalid.
            Result IsNotQuerySat(Microsoft.Boogie.Expr Query, out IAssignment assignment);
        }

        public interface IAssignment
        {
            Microsoft.Boogie.LiteralExpr GetAssignment(SymbolicVariable SV);
        }
    }
}

