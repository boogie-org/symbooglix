using System;
using symbooglix;

namespace symbooglix
{
	// Handy class that clients can override if they only want to handle a few events
	public class ContinuingHandler : IExecutorHandler
	{
		virtual public Executor.HandlerAction handle(Microsoft.Boogie.AssertCmd c, Executor executor)
		{
			return Executor.HandlerAction.CONTINUE;
		}

		virtual public Executor.HandlerAction handle(Microsoft.Boogie.AssignCmd c, Executor executor)
		{
			return Executor.HandlerAction.CONTINUE;
		}

		virtual public Executor.HandlerAction handle(Microsoft.Boogie.AssumeCmd c, Executor executor)
		{
			return Executor.HandlerAction.CONTINUE;
		}

		virtual public Executor.HandlerAction handle(Microsoft.Boogie.AssertEnsuresCmd c, Executor executor)
		{
			return Executor.HandlerAction.CONTINUE;
		}

		virtual public Executor.HandlerAction handle(Microsoft.Boogie.AssertRequiresCmd c, Executor executor)
		{
			return Executor.HandlerAction.CONTINUE;
		}

		virtual public Executor.HandlerAction handle(Microsoft.Boogie.CallCmd c, Executor executor)
		{
			return Executor.HandlerAction.CONTINUE;
		}

		virtual public Executor.HandlerAction handle(Microsoft.Boogie.GotoCmd c, Executor executor)
		{
			return Executor.HandlerAction.CONTINUE;
		}

		virtual public Executor.HandlerAction handle (Microsoft.Boogie.HavocCmd c, Executor executor)
		{
			return Executor.HandlerAction.CONTINUE;
		}

		virtual public Executor.HandlerAction handle(Microsoft.Boogie.ReturnCmd c, Executor executor)
		{
			return Executor.HandlerAction.CONTINUE;
		}

		virtual public Executor.HandlerAction handle(Microsoft.Boogie.YieldCmd c, Executor executor)
		{
			return Executor.HandlerAction.CONTINUE;
		}
		virtual public Executor.HandlerAction enterProcedure(Microsoft.Boogie.Implementation p, System.Collections.Generic.List<Microsoft.Boogie.Expr> procedureParams, Executor executor)
		{
			return Executor.HandlerAction.CONTINUE;
		}
	}
}

