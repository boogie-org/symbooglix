//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
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
            
            msg += args.State.TerminationType.GetMessage();


            if (args.State.TerminationType is TerminatedAtUnsatisfiableAxiom)
            {
                var tt = args.State.TerminationType as TerminatedAtUnsatisfiableAxiom;
                var enforced = tt.ExitLocation.AsAxiom.FindAttribute("symbooglix_enforce_unique");
                if (enforced != null)
                    msg += System.Environment.NewLine + "This axiom was generated to enforce the unique keyword.";

                if (args.State.Speculative)
                {
                    // FIXME: This specific to the SymbooglixDriver and is not general. Right now it's quite useful
                    // to tell users this though.
                    msg += System.Environment.NewLine + System.Environment.NewLine +
                        "Note this is a speculative failure because the solver" +
                        " could not prove that the axiom is satisfiable. If you trust your axioms then you" +
                        " can disable checking them by using --check-entry-axioms=0";
                }
            }

            WriteLine(color, msg);
        }
    }
}

