using System;
using Symbooglix;
using Microsoft.Boogie;

namespace Symbooglix
{
    public interface IBreakPointHandler
    {
        Executor.HandlerAction handleBreakPoint(string name, Executor e);
    }

    public class BreakPointPrinter : IBreakPointHandler
    {
        public Executor.HandlerAction handleBreakPoint(string name, Executor e)
        {
            Console.ForegroundColor = ConsoleColor.DarkMagenta;
            Console.WriteLine("Hit break point " + name);
            Console.ResetColor();
            return Executor.HandlerAction.CONTINUE;
        }
    }
}
