using System;
using Symbooglix;
using Microsoft.Boogie;
using System.Collections.Generic;

namespace Symbooglix
{
    // This should be installed as a pre-event handler to work correctly
    public class EnterAndLeaveStackPrinter : ContinuingHandler
    {
        public override Executor.HandlerAction handle(ReturnCmd c, Executor executor)
        {
            Console.WriteLine("Leaving procedure. Printing its stack");
            Console.Write(executor.currentState.getCurrentStackFrame().ToString());
            return Executor.HandlerAction.CONTINUE;
        }

        public override Executor.HandlerAction enterProcedure(Implementation p, List<Expr> procedureParams, Executor executor)
        {
            Console.WriteLine("Entering new procedure. Printing stack of caller");
            Console.Write(executor.currentState.getCurrentStackFrame().ToString());
            return Executor.HandlerAction.CONTINUE;
        }
    }
}

