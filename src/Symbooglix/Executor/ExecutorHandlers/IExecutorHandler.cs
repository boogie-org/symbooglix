using Microsoft.Boogie;
using System;
using System.Collections.Generic;

namespace Symbooglix
{
    public interface IExecutorHandler
    {
        // Visit Cmd events
        Executor.HandlerAction Handle(AssertCmd c, Executor executor);
        Executor.HandlerAction Handle(AssignCmd c, Executor executor);
        Executor.HandlerAction Handle(AssumeCmd c, Executor executor);
        //Executor.HandlerAction handle(CommentCmd c, Executor executor);
        Executor.HandlerAction Handle(AssertEnsuresCmd c, Executor executor);
        Executor.HandlerAction Handle(AssertRequiresCmd c, Executor executor);
        //Executor.HandlerAction handle(LoopInitAssertCmd c, Executor executor);
        //Executor.HandlerAction handle(LoopInvMaintainedAssertCmd c, Executor executor;
        Executor.HandlerAction Handle(CallCmd c, Executor executor);
        Executor.HandlerAction Handle(GotoCmd c, Executor executor);
        Executor.HandlerAction Handle(HavocCmd c, Executor executor);
        //Executor.HandlerAction handle(ParCallCmd c, Executor executor);
        Executor.HandlerAction Handle(ReturnCmd c, Executor executor);
        //Executor.HandlerAction handle(StateCmd c, Executor executor);
        Executor.HandlerAction Handle(YieldCmd c, Executor executor);

        Executor.HandlerAction EnterImplementation(Implementation impl, List<Expr> procedureParams, Executor executor);
        Executor.HandlerAction EnterAndLeaveProcedure(Procedure proc, List<Expr> procedureParams, Executor executor);
    }
}

