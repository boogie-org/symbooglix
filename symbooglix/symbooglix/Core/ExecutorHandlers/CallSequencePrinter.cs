using System;
using symbooglix;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace symbooglix
{
    // This should be used a pre-event handler
    public class CallSequencePrinter : ContinuingHandler
    {
        public CallSequencePrinter()
        {
        }

        public override Executor.HandlerAction handle(ReturnCmd c, Executor executor)
        {
            Console.WriteLine("Leaving: " + executor.currentState.getCurrentStackFrame().procedure.Name + "()");
            return Executor.HandlerAction.CONTINUE;
        }

        public override Executor.HandlerAction enterProcedure(Implementation p, List<Expr> procedureParams, Executor executor)
        {
            Console.Write("Calling: " + p.Name + "(");

            for (int argidx = 0; argidx < procedureParams.Count; ++argidx)
            {
                Console.Write(procedureParams[argidx]);

                if (argidx < ( procedureParams.Count - 1 ))
                    Console.Write(", ");
            }
            Console.WriteLine(")");

            return Executor.HandlerAction.CONTINUE;
        }

    }
}

