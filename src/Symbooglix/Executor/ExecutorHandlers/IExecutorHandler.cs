using Microsoft.Boogie;
using System;
using System.Collections.Generic;

namespace Symbooglix
{
    public interface IExecutorHandler
    {
        // Visit Cmd events
        void Handle(AssertCmd c, Executor executor);
        void Handle(AssignCmd c, Executor executor);
        void Handle(AssumeCmd c, Executor executor);
        //void handle(CommentCmd c, Executor executor);
        void Handle(AssertEnsuresCmd c, Executor executor);
        void Handle(AssertRequiresCmd c, Executor executor);
        //void handle(LoopInitAssertCmd c, Executor executor);
        //void handle(LoopInvMaintainedAssertCmd c, Executor executor;
        void Handle(CallCmd c, Executor executor);
        void Handle(GotoCmd c, Executor executor);
        void Handle(HavocCmd c, Executor executor);
        //void handle(ParCallCmd c, Executor executor);
        void Handle(ReturnCmd c, Executor executor);
        //void handle(StateCmd c, Executor executor);
        void Handle(YieldCmd c, Executor executor);

        void EnterImplementation(Implementation impl, List<Expr> procedureParams, Executor executor);
        void EnterAndLeaveProcedure(Procedure proc, List<Expr> procedureParams, Executor executor);
    }
}

