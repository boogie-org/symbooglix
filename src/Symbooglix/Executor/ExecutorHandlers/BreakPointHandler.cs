using System;
using Symbooglix;
using Microsoft.Boogie;

namespace Symbooglix
{
    public class BreakPointPrinter
    {
        static public void handleBreakPoint(object executor, Executor.BreakPointEventArgs eventArgs)
        {
            Console.ForegroundColor = ConsoleColor.DarkMagenta;
            Console.WriteLine("Hit break point " + eventArgs.Name);
            Console.ResetColor();
        }
    }
}
