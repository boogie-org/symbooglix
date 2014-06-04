using System;
using System.Collections.Generic;

namespace symbooglix
{
    public interface ISolver
    {
        void SetConstraints(ConstraintManager cm);

        // This can be used as a hint to the solver to destroy Constraints created internally in the solver
        void DropConstraints();

        // Given the constraints is the query expression satisfiable
        // \return True iff sat
        // if sat the assignment will be set to an assignment object
        //
        // If another query is made the previously received assignment object may be
        // invalid.
        bool IsQuerySat(Microsoft.Boogie.Expr Query, out IAssignment assignment);

        // Given the constraints is the negation of the query expression satisfiable
        // \return True iff sat
        // if sat the assignment will be set to an assignment object
        //
        // If another query is made the previously received assignment object may be
        // invalid.
        bool IsNotQuerySat(Microsoft.Boogie.Expr Query, out IAssignment assignment);
    }

    public interface IAssignment
    {
        Microsoft.Boogie.LiteralExpr GetAssignment(SymbolicVariable SV);
    }
}

