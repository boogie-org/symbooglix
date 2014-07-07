using System;
using Symbooglix;
using System.Collections.Generic;
using Microsoft.Boogie;

namespace Symbooglix
{
    // This should be used a pre-event handler
    public class CallSequencePrinter : ContinuingHandler
    {
        public CallSequencePrinter()
        {
        }

        public override Executor.HandlerAction Handle(ReturnCmd c, Executor executor)
        {
            Console.WriteLine("Leaving: " + executor.currentState.GetCurrentStackFrame().Impl.Name + "()");
            return Executor.HandlerAction.CONTINUE;
        }

        public override Executor.HandlerAction EnterImplementation(Implementation impl, List<Expr> procedureParams, Executor executor)
        {
            Console.Write("Calling: " + impl.Name + "(");

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

