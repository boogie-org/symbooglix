using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public class TerminationConsoleReporter : ITerminationHandler
    {
        public TerminationConsoleReporter()
        {
        }

        public static void WriteLine(ConsoleColor Colour ,string msg)
        {
            var savedColour = Console.ForegroundColor;
            Console.ForegroundColor = Colour;
            Console.WriteLine(msg);
            Console.ForegroundColor = savedColour;
        }


        public void handleSuccess(ExecutionState s)
        {
            string msg = "State " + s.id + " terminated without error";
            WriteLine(ConsoleColor.Green, msg);
        }

        public void handleFailingAssert(ExecutionState s)
        {
            string msg = "State " + s.id + " terminated with an error";
            WriteLine(ConsoleColor.Red, msg);
            Debug.Assert(s.getCurrentStackFrame().currentInstruction.Current is AssertCmd);
            var failingCmd = (AssertCmd) s.getCurrentStackFrame().currentInstruction.Current;
            msg = "The following assertion failed\n" +
                  failingCmd.tok.filename + ":" + failingCmd.tok.line + ": " +
                  failingCmd.ToString();
            WriteLine(ConsoleColor.DarkRed, msg);


            s.dumpState();
        }

        public void handleUnsatisfiableRequires(ExecutionState s, Microsoft.Boogie.Requires requiresStatement)
        {
            string msg = "State " + s.id + " terminated with an error";
            WriteLine(ConsoleColor.Red, msg);
            msg = "The following requires statement could not be satisfied\n" +
                  requiresStatement.tok.filename + ":" + requiresStatement.tok.line + ": " +
                  requiresStatement.Condition.ToString();
            WriteLine(ConsoleColor.DarkRed, msg);

            s.dumpState();
        }

        public void handleFailingEnsures (ExecutionState s, Ensures ensuresStatement)
        {
            string msg = "State " + s.id + " terminated with an error";
            WriteLine(ConsoleColor.Red, msg);
            Debug.Assert(s.getCurrentStackFrame().currentInstruction.Current is ReturnCmd);
            msg = "The following ensures failed\n" +
                  ensuresStatement.tok.filename + ":" + ensuresStatement.tok.line + ": " +
                  ensuresStatement.Condition.ToString();
            WriteLine(ConsoleColor.DarkRed, msg);


            s.dumpState();
        }

        public void handleUnsatisfiableAssume(ExecutionState s)
        {
            AssumeCmd assumeCmd = (AssumeCmd) s.getCurrentStackFrame().currentInstruction.Current;

            // Most of the time we should inform about failing assumes, this hack prevents
            // emitting messages about assumes related to control flow.
            if (QKeyValue.FindBoolAttribute(assumeCmd.Attributes, "partition") == false)
            {
                string msg = "State " + s.id + " terminated";
                WriteLine(ConsoleColor.DarkMagenta, msg);
                Debug.Assert(s.getCurrentStackFrame().currentInstruction.Current is AssumeCmd);
                var failingCmd = (AssumeCmd) s.getCurrentStackFrame().currentInstruction.Current;
                msg = "The following assumption is unsatisfiable\n" +
                failingCmd.tok.filename + ":" + failingCmd.tok.line + ": " +
                failingCmd.ToString();
                WriteLine(ConsoleColor.DarkMagenta, msg);


                s.dumpState();
            }
        }
    }
}

