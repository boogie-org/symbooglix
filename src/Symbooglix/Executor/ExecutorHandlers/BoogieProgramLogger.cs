using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using Symbooglix.Util;
using Microsoft.Boogie;
using System.Linq;

namespace Symbooglix
{
    public class BoogieProgramLogger : IExecutorEventHandler
    {
        private string Directory;

        public string ProgramDestination
        {
            get;
            private set;
        }

        public string CallGrindFileDestintation
        {
            get;
            private set;
        }

        public BoogieProgramLogger(string directory)
        {
            this.Directory = directory;
            this.ProgramDestination = Path.Combine(Directory, "program.bpl");
            this.CallGrindFileDestintation = Path.Combine(Directory, "instr_stats.callgrind");
        }

        public void Connect(Executor e)
        {
            e.ExecutorTerminated += HandleExecutorTerminated;
        }

        void HandleExecutorTerminated(object sender, Executor.ExecutorTerminatedArgs e)
        {
            var executor = sender as Executor;
            Debug.Assert(sender is Executor, "Expected Executor");

            Program clonedProgram = null;
            using (var SW = new StreamWriter(this.ProgramDestination))
            {
                // FIXME: Duplication isn't ideal here but we don't want to affect the reported error locations
                // which would happen if we changed the tokens on the Executor's program
                var duplicator = new DuplicatorResolvingGotoInstructionStatistics();
                clonedProgram = (Program) duplicator.Visit(executor.TheProgram);
                Console.WriteLine("Writing unstructured program to {0}", this.ProgramDestination);
                ProgramPrinter.Print(clonedProgram, SW, /*pretty=*/false, ProgramDestination, /*setTokens=*/ true, ProgramPrinter.PrintType.UNSTRUCTURED_ONLY);
            }

            // Write out instruction statistics to a callgrind file
            using (var SW = new StreamWriter(this.CallGrindFileDestintation))
            {
                Console.WriteLine("Writing callgrind file to {0}", this.CallGrindFileDestintation);
                var callGrindFilePrinter = new CallGrindFilePrinter(clonedProgram, Path.GetFileName(this.ProgramDestination));
                callGrindFilePrinter.Print(SW);
            }
        }

        public void Disconnect(Executor e)
        {
            e.ExecutorTerminated -= HandleExecutorTerminated;
        }
    }

    class DuplicatorResolvingGotoInstructionStatistics : Duplicator
    {
        public override Implementation VisitImplementation(Implementation node)
        {
            var newImpl = base.VisitImplementation(node);

            // FIXME: The Duplicator already has this map but doesn't share it

            // Build mapping of old -> new Blocks
            var blockMap = new Dictionary<Block,Block>();

            foreach (var pair in node.Blocks.Zip(newImpl.Blocks))
            {
                blockMap.Add(pair.Item1, pair.Item2);
            }

            // Remap goto Instruction statistics
            foreach (var gotoCmd in newImpl.Blocks.Select( bb => bb.TransferCmd).OfType<GotoCmd>())
            {
                // Make a copy
                var newGotoStats = ( gotoCmd.GetInstructionStatistics() as GotoInstructionStatistics ).BlockSubstitution(blockMap);
                gotoCmd.SetMetadata((int) Annotation.AnnotationIndex.PROFILE_DATA, newGotoStats);
            }

            return newImpl;
        }

    }
}

