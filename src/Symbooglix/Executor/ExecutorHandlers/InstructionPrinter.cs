using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public class InstructionPrinter : IExecutorHandler
    {
        public Executor.HandlerAction Handle(AssertCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction Handle(AssignCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction Handle(AssumeCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction Handle(AssertEnsuresCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction Handle(AssertRequiresCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction Handle(CallCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction Handle(GotoCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction Handle(HavocCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction Handle(ReturnCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction Handle(YieldCmd c, Executor executor)
        {
            return print(c);
        }

        public Executor.HandlerAction EnterImplementation(Implementation impl, List<Expr> procedureParams, Executor executor)
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

