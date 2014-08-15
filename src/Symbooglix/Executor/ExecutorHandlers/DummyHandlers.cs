using System;
using Symbooglix;

namespace Symbooglix
{
    // Handy class that clients can override if they only want to handle a few events
    public class ContinuingHandler : IExecutorHandler
    {
        virtual public Executor.HandlerAction Handle(Microsoft.Boogie.AssertCmd c, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }

        virtual public Executor.HandlerAction Handle(Microsoft.Boogie.AssignCmd c, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }

        virtual public Executor.HandlerAction Handle(Microsoft.Boogie.AssumeCmd c, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }

        virtual public Executor.HandlerAction Handle(Microsoft.Boogie.AssertEnsuresCmd c, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }

        virtual public Executor.HandlerAction Handle(Microsoft.Boogie.AssertRequiresCmd c, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }

        virtual public Executor.HandlerAction Handle(Microsoft.Boogie.CallCmd c, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }

        virtual public Executor.HandlerAction Handle(Microsoft.Boogie.GotoCmd c, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }

        virtual public Executor.HandlerAction Handle (Microsoft.Boogie.HavocCmd c, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }

        virtual public Executor.HandlerAction Handle(Microsoft.Boogie.ReturnCmd c, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }

        virtual public Executor.HandlerAction Handle(Microsoft.Boogie.YieldCmd c, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }
        virtual public Executor.HandlerAction EnterImplementation(Microsoft.Boogie.Implementation impl, System.Collections.Generic.List<Microsoft.Boogie.Expr> procedureParams, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }

        virtual public Executor.HandlerAction EnterAndLeaveProcedure(Microsoft.Boogie.Procedure proc, System.Collections.Generic.List<Microsoft.Boogie.Expr> procedureParams, Executor executor)
        {
            return Executor.HandlerAction.CONTINUE;
        }
    }
}

