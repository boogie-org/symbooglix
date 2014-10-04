using System;
using System.Diagnostics;
using System.IO;
using Symbooglix.Util;

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
            e.ExecutorStarted += HandleExecutorStarted;
        }

        void HandleExecutorStarted(object sender, Executor.ExecutorStartedArgs e)
        {
            var executor = sender as Executor;
            Debug.Assert(sender is Executor, "Expected Executor");

            using (var SW = new StreamWriter(this.Destination))
            {
                Console.WriteLine("Writing unstructured program to {0}", this.Destination);
                ProgramPrinter.Print(executor.TheProgram, SW, /*pretty=*/false, ProgramPrinter.PrintType.UNSTRUCTURED_ONLY);
            }
        }

        public void Disconnect(Executor e)
        {
            e.ExecutorStarted -= HandleExecutorStarted;
        }
    }
}

