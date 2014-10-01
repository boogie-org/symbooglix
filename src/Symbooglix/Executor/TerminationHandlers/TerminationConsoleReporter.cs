using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public class TerminationConsoleReporter : IExecutorEventHandler
    {
        public TerminationConsoleReporter()
        {
        }

        public static void WriteLine(ConsoleColor Colour ,string msg)
        {
            Console.ForegroundColor = Colour;
            Console.WriteLine(msg);
            Console.ResetColor();
        }

        public void Connect(Executor e)
        {
            e.StateTerminated += handle;
        }

        public void Disconnect(Executor e)
        {
            e.StateTerminated -= handle;
        }

        private void handle(Object executor, Executor.ExecutionStateEventArgs args)
        {
            string msg = "State " + args.State.Id + ":" + (args.State.Speculative ? "(Speculative) " : " ");

            ConsoleColor color;
            if (args.State.TerminationType is TerminatedWithoutError)
                color = ConsoleColor.Green;
            else if (args.State.TerminationType is TerminatedAtUnsatisfiableAssume)
            {
                var assumeCmd = args.State.TerminationType.ExitLocation.AsCmd as AssumeCmd;

                // We don't want to notify about unsatisfiable assumes that are a result
                // of control flow (i.e. goto follow by an assume)
                if (QKeyValue.FindBoolAttribute(assumeCmd.Attributes, "partition"))
                    return;

                color = ConsoleColor.DarkMagenta;
            }
            else
                color = ConsoleColor.Red;
            

            WriteLine(color, msg + args.State.TerminationType.GetMessage());

            // FIXME: Remove me
            args.State.Dump();
        }
    }
}

