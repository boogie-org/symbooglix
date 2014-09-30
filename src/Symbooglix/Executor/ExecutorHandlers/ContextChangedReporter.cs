using System;

namespace Symbooglix
{
    public class ContextChangedReporter : IExecutorEventHandler
    {
        public ContextChangedReporter()
        {
        }

        private void handle(Object executor, Executor.ContextChangeEventArgs contextChangedEventArgs)
        {
            var oldState = contextChangedEventArgs.Previous;
            var newState = contextChangedEventArgs.Next;

            Console.ForegroundColor = ConsoleColor.DarkBlue;
            Console.BackgroundColor = ConsoleColor.Yellow;
            Console.WriteLine("[Context changed " + oldState.Id + " => " + newState.Id + "]");
            Console.ResetColor();
        }

        public void Connect(Executor e)
        {
            e.ContextChanged += handle;
        }

        public void Disconnect(Executor e)
        {
            e.ContextChanged -= handle;
        }
    }
}

