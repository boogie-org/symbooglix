using System;
using Symbooglix;
using Microsoft.Boogie;
using System.Diagnostics;

namespace Symbooglix
{
    public class BreakPointPrinter
    {
        static public void handleBreakPoint(object executor, Executor.BreakPointEventArgs eventArgs)
        {
            Console.ForegroundColor = ConsoleColor.DarkMagenta;
            Console.WriteLine("Hit break point " + eventArgs.Name);

            if (Debugger.IsAttached)
            {
                Debugger.Break();
            }
            else
            {
                Console.WriteLine("Could not Break because debugger was not attached");
            }
            Console.ResetColor();
        }
    }
}
