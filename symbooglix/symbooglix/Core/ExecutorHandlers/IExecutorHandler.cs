using Microsoft.Boogie;
using System;
using System.Collections.Generic;

namespace symbooglix
{
	public interface IExecutorHandler
	{
		// Visit Cmd events
		Executor.HandlerAction handle(AssertCmd c, Executor executor);
		Executor.HandlerAction handle(AssignCmd c, Executor executor);
		Executor.HandlerAction handle(AssumeCmd c, Executor executor);
		//Executor.HandlerAction handle(CommentCmd c, Executor executor);
		Executor.HandlerAction handle(AssertEnsuresCmd c, Executor executor);
		Executor.HandlerAction handle(AssertRequiresCmd c, Executor executor);
		//Executor.HandlerAction handle(LoopInitAssertCmd c, Executor executor);
		//Executor.HandlerAction handle(LoopInvMaintainedAssertCmd c, Executor executor;
		Executor.HandlerAction handle(CallCmd c, Executor executor);
		Executor.HandlerAction handle(GotoCmd c, Executor executor);
		Executor.HandlerAction handle(HavocCmd c, Executor executor);
		//Executor.HandlerAction handle(ParCallCmd c, Executor executor);
		Executor.HandlerAction handle(ReturnCmd c, Executor executor);
		//Executor.HandlerAction handle(StateCmd c, Executor executor);
		Executor.HandlerAction handle(YieldCmd c, Executor executor);

		Executor.HandlerAction enterProcedure(Implementation p, List<Expr> procedureParams, Executor executor);
	}
}

