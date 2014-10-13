using System;
using System.IO;

namespace Symbooglix
{
    public class InstructionPrinter : IExecutorEventHandler
    {
        TextWriter TW;
        public InstructionPrinter(TextWriter TW)
        {
            this.TW = TW;
        }

        private void handle(Object executor, Executor.InstructionVisitEventArgs instructionVisitEventArgs)
        {
            var loc = instructionVisitEventArgs.Location;
            TW.WriteLine(loc.FileName + ":" + loc.LineNumber + ": " + loc.ToString().TrimEnd('\n'));
        }

        public void Connect(Executor e)
        {
            e.InstructionVisited += handle;
        }

        public void Disconnect(Executor e)
        {
            e.InstructionVisited -= handle;
        }
    }
}

