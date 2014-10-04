using System;
using System.Diagnostics;
using System.IO;
using Symbooglix.Util;
using Microsoft.Boogie;

namespace Symbooglix
{
    public class BoogieProgramLogger : IExecutorEventHandler
    {
        private string Directory;

        public string Destination
        {
            get;
            private set;
        }

        public BoogieProgramLogger(string directory)
        {
            this.Directory = directory;
            this.Destination = Path.Combine(Directory, "program.bpl");
        }

        public void Connect(Executor e)
        {
            e.ExecutorTerminated += HandleExecutorTerminated;
        }

        void HandleExecutorTerminated(object sender, Executor.ExecutorTerminatedArgs e)
        {
            var executor = sender as Executor;
            Debug.Assert(sender is Executor, "Expected Executor");

            using (var SW = new StreamWriter(this.Destination))
            {
                // FIXME: Duplication isn't ideal here but we don't want to affect the reported error locations
                // which would happen if we changed the tokens on the Executor's program
                var duplicator = new Duplicator();
                var clonedProgram = (Program) duplicator.Visit(executor.TheProgram);
                Console.WriteLine("Writing unstructured program to {0}", this.Destination);
                ProgramPrinter.Print(clonedProgram, SW, /*pretty=*/false, Destination, /*setTokens=*/ true, ProgramPrinter.PrintType.UNSTRUCTURED_ONLY);
            }
        }

        public void Disconnect(Executor e)
        {
            e.ExecutorTerminated -= HandleExecutorTerminated;
        }
    }
}

