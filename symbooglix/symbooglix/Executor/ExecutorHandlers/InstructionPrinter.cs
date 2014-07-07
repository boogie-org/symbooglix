using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public class InstructionPrinter : IExecutorHandler
    {
        public Executor.HandlerAction handle(AssertCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction handle(AssignCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction handle(AssumeCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction handle(AssertEnsuresCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction handle(AssertRequiresCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction handle(CallCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction handle(GotoCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction handle(HavocCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction handle(ReturnCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction handle(YieldCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction enterProcedure(Implementation p, List<Expr> procedureParams, Executor executor)
        {
            // This isn't an actual instruction so do nothing
            return Executor.HandlerAction.CONTINUE;
        }

        private Executor.HandlerAction print(Absy cmd)
        {
            string cmdStr = cmd.ToString();
            cmdStr = cmdStr.TrimEnd('\n'); // Some command have newlines and others don't
            Console.Error.WriteLine("InstructionPrinter: " + cmdStr);
            return Executor.HandlerAction.CONTINUE;
        }
    }
}

