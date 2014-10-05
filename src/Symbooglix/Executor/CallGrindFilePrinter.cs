using System;
using Microsoft.Boogie;
using System.IO;
using System.Linq;
using System.Diagnostics;

namespace Symbooglix
{
    public class CallGrindFilePrinter
    {
        Program TheProgram;
        TextWriter TW;
        string PathToProgram;

        public CallGrindFilePrinter(Program prog, string pathToProgram)
        {
            this.TheProgram = prog;
            this.PathToProgram = pathToProgram;
        }

        protected void PrintCostLine(int line, InstructionStatistics instrStats)
        {
            TW.WriteLine("{0} {1} {2} {3}", line, instrStats.Covered, instrStats.Terminations, instrStats.Forks);
        }

        protected void Print(Block bb, Implementation impl)
        {
            TW.WriteLine("# BasicBlock:{0}", bb.Label);

            // Handle Commands
            foreach (var cmd in bb.Cmds)
            {
                if (cmd is CallCmd)
                {
                    var callCmd = cmd as CallCmd;
                    TW.WriteLine("# Call into {0}", callCmd.Proc.Name);
                    TW.WriteLine("cfn={0}", callCmd.Proc.Name);

                    // FIXME: There should be a special statistics for CallCmd which records the target because
                    // we are duplication logic of the Executor here which could change
                    // Determine if call would of been to a Procedure or Impl
                    var calleeImpl = TheProgram.TopLevelDeclarations.OfType<Implementation>().Where(x => x.Name == callCmd.Proc.Name);
                    int calleeLineNumber = 0;
                    if (calleeImpl.Count() > 0)
                    {
                        TW.WriteLine("# Call into implementation");
                        calleeLineNumber = calleeImpl.First().tok.line;
                    }
                    else
                    {
                        TW.WriteLine("# Call into procedure");
                        calleeLineNumber = callCmd.Proc.tok.line;
                    }


                    TW.WriteLine("calls={0} {1}", callCmd.GetInstructionStatistics().Covered, calleeLineNumber);

                    // FIXME: This is supposed to be the inclusive "cost" of calls to the proc/impl.
                    // We aren't sending the right number. We really need to walk to call graph bottom up
                    // instead of iterating over the impl/proc in an arbitrary order
                    PrintCostLine(callCmd.tok.line, callCmd.GetInstructionStatistics());

                    TW.WriteLine("cfn={0}", impl.Name);
                }
                else
                {
                    PrintCostLine(cmd.tok.line, cmd.GetInstructionStatistics());
                }
            }


            // Handle TransferCmd
            if (bb.TransferCmd is ReturnCmd)
            {
                PrintCostLine(bb.TransferCmd.tok.line, bb.TransferCmd.GetInstructionStatistics());
            }
            else
            {
                Debug.Assert(bb.TransferCmd is GotoCmd);
                var gotoCmd = bb.TransferCmd as GotoCmd;

                var gotoCmdStats = gotoCmd.GetInstructionStatistics() as GotoInstructionStatistics;

                if (gotoCmd.labelTargets.Count == 1)
                {
                    // Non conditional jump
                    int targetLineNumber = GetBlockLineNumber(gotoCmd.labelTargets[0]);
                    TW.WriteLine("jump={0} {1}", gotoCmdStats.TotalJumps, targetLineNumber);
                    TW.WriteLine("{0}", gotoCmd.tok.line);
                }
                else
                {
                    // Conditional jump
                    foreach (var target in gotoCmd.labelTargets)
                    {
                        int targetLineNumber = GetBlockLineNumber(target);
                        TW.WriteLine("jcnd={0}/{1} {2}", gotoCmdStats.GetJumpsTo(target), gotoCmdStats.TotalJumps, targetLineNumber);
                        TW.WriteLine("{0}", gotoCmd.tok.line);
                    }
                }
                PrintCostLine(gotoCmd.tok.line, gotoCmdStats);
            }
        }

        private int GetBlockLineNumber(Block bb)
        {
            int line = bb.tok.line;

            // FIXME: There is a Bug in Boogie somewhere because the Tokens attached to the program are wrong!
            #if DEBUG
            string filename = Path.GetFileName(bb.tok.filename);
            Debug.Assert(filename == Path.GetFileName(PathToProgram), "Mismatched tokens. Expected " + Path.GetFileName(PathToProgram) + ", got " + filename);
            #endif
            return line;
        }

        protected void Print(Implementation impl)
        {
            TW.WriteLine("# Statistics for {0}", impl.Name);
            TW.WriteLine("fn={0}", impl.Name);

            var proc = impl.Proc;
            TW.WriteLine("# Requires statements Start");
            foreach (var requires in proc.Requires)
            {
                PrintCostLine(requires.tok.line, requires.GetInstructionStatistics());
            }
            TW.WriteLine("# Requires statements End");
            TW.WriteLine("# Ensures statements Start");
            foreach (var ensures in proc.Ensures)
            {
                PrintCostLine(ensures.tok.line, ensures.GetInstructionStatistics());
            }
            TW.WriteLine("# Ensures statements End");

            foreach (var bb in impl.Blocks)
            {
                Print(bb, impl);
            }
        }

        public void Print(TextWriter TW)
        {
            this.TW = TW;
            TW.WriteLine("# Callgrind file generated by Symbooglix");
            TW.WriteLine("# This file can be opened by KCacheGrind");

            // List supported counters
            TW.WriteLine("events: Covered Terminations Forks");

            // Specifiy input file
            TW.WriteLine("fl={0}", this.PathToProgram);

            // FIXME: Walk up callgraph instead
            foreach (var impl in TheProgram.TopLevelDeclarations.OfType<Implementation>())
            {
                Print(impl);
            }
        }
    }
}

