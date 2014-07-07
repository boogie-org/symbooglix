using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using Symbooglix;

namespace Symbooglix
{
    // This Handler is for debugging and should be registered as a pre-event and post-event handler.
    // On being called as a pre-event handler it records properties about the executed command
    // On being called as a post-event handler it verifies that the previously recorded properties have not changed
    //
    // The rationale for having this is we should probably not be modifying the program as we are executing
    public class VerifyUnmodifiedProcedureHandler : IExecutorHandler
    {
        private Absy oldRef = null;
        private string oldString = null;


        public VerifyUnmodifiedProcedureHandler()
        {
        }

        private void reset()
        {
            oldRef = null;
            oldString = null;
        }

        private bool isRecord()
        {
            return oldRef == null && oldString == null;
        }

        private Executor.HandlerAction helper(Absy c)
        {
            if (isRecord())
            {
                oldRef = c;
                oldString = c.ToString();
            }
            else
            {
                // Verify
                if (!Object.ReferenceEquals(oldRef, c))
                    throw new InvalidProgramException("Program was unintensionally modified");

                if (oldString != c.ToString())
                    throw new InvalidProgramException("Program was unintensionally modified");

                reset();
            }
            return Executor.HandlerAction.CONTINUE;
        }

        public Executor.HandlerAction handle(AssertCmd c, Executor executor)
        {
            return helper(c);
        }

        public Executor.HandlerAction handle(AssignCmd c, Executor executor)
        {
            return helper(c);
        }

        public Executor.HandlerAction handle(AssumeCmd c, Executor executor)
        {
            return helper(c);
        }

        public Executor.HandlerAction handle(AssertEnsuresCmd c, Executor executor)
        {
            return helper(c);
        }

        public Executor.HandlerAction handle(AssertRequiresCmd c, Executor executor)
        {
            return helper(c);
        }

        public Executor.HandlerAction handle(CallCmd c, Executor executor)
        {
            return helper(c);
        }

        public Executor.HandlerAction handle(GotoCmd c, Executor executor)
        {
            return helper(c);
        }

        public Executor.HandlerAction handle(HavocCmd c, Executor executor)
        {
            return helper(c);
        }

        public Executor.HandlerAction handle(ReturnCmd c, Executor executor)
        {
            return helper(c);
        }

        public Executor.HandlerAction handle(YieldCmd c, Executor executor)
        {
            return helper(c);
        }

        public Executor.HandlerAction enterProcedure(Implementation p, List<Expr> procedureParams, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }
    }
}

