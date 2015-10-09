//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using System.Collections.Generic;
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
        Implementation EntryPoint;

        public CallGrindFilePrinter(Program prog, string pathToProgram, Implementation entryPoint)
        {
            this.TheProgram = prog;
            this.PathToProgram = pathToProgram;
            this.EntryPoint = entryPoint;
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
                        calleeLineNumber = GetLineNumber(calleeImpl.First());
                    }
                    else
                    {
                        TW.WriteLine("# Call into procedure");
                        calleeLineNumber = GetLineNumber(callCmd.Proc);
                    }


                    TW.WriteLine("calls={0} {1}", callCmd.GetInstructionStatistics().Covered, calleeLineNumber);

                    // FIXME: This is supposed to be the inclusive "cost" of calls to the proc/impl.
                    // We aren't sending the right number. We really need to walk to call graph bottom up
                    // instead of iterating over the impl/proc in an arbitrary order
                    PrintCostLine(GetLineNumber(callCmd), callCmd.GetInstructionStatistics());

                    TW.WriteLine("cfn={0}", impl.Name);
                }
                else
                {
                    PrintCostLine(GetLineNumber(cmd), cmd.GetInstructionStatistics());
                }
            }


            // Handle TransferCmd
            if (bb.TransferCmd is ReturnCmd)
            {
                PrintCostLine(GetLineNumber(bb.TransferCmd), bb.TransferCmd.GetInstructionStatistics());
            }
            else
            {
                Debug.Assert(bb.TransferCmd is GotoCmd);
                var gotoCmd = bb.TransferCmd as GotoCmd;

                var gotoCmdStats = gotoCmd.GetInstructionStatistics() as GotoInstructionStatistics;

                if (gotoCmd.labelTargets.Count == 1)
                {
                    // Non conditional jump
                    TW.WriteLine("jump={0} {1}", gotoCmdStats.Covered, GetLineNumber(gotoCmd.labelTargets[0]));
                    TW.WriteLine("{0}", GetLineNumber(gotoCmd));
                }
                else
                {
                    // Conditional jump
                    foreach (var target in gotoCmd.labelTargets)
                    {
                        // Note we use gotoCmdStats.Covered instead of gotoCmdStats.TotalJumps. The reason is that using
                        // TotalJumps can be confusing because this number can be greater than the number of times the
                        // GotoCmd was visited. E.g. We could say "4 out 9 times went to ..." when the GotoCmd was only visited
                        // 5 times.
                        TW.WriteLine("jcnd={0}/{1} {2}", gotoCmdStats.GetJumpsTo(target), gotoCmdStats.Covered, GetLineNumber(target));
                        TW.WriteLine("{0}", GetLineNumber(gotoCmd));
                    }
                }
                PrintCostLine(gotoCmd.tok.line, gotoCmdStats);
            }
        }

        private int GetLineNumber(Absy node)
        {
            int line = node.tok.line;
            #if DEBUG
            string filename = Path.GetFileName(node.tok.filename);
            Debug.Assert(filename == Path.GetFileName(PathToProgram), "Mismatched tokens. Expected " + Path.GetFileName(PathToProgram) + ", got " + filename);
            #endif
            return line;
        }

        protected void Print(Implementation impl)
        {
            Print(impl.Proc);

            foreach (var bb in impl.Blocks)
            {
                Print(bb, impl);
            }
        }

        protected void Print(Procedure proc)
        {
            TW.WriteLine("# Statistics for {0}", proc.Name);
            TW.WriteLine("fn={0}", proc.Name);

            TW.WriteLine("# Requires statements Start");
            foreach (var requires in proc.Requires)
            {
                PrintCostLine(GetLineNumber(requires), requires.GetInstructionStatistics());
            }
            TW.WriteLine("# Requires statements End");
            TW.WriteLine("# Ensures statements Start");
            foreach (var ensures in proc.Ensures)
            {
                PrintCostLine(GetLineNumber(ensures), ensures.GetInstructionStatistics());
            }
            TW.WriteLine("# Ensures statements End");
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

            TW.WriteLine("# Start Axioms");
            TW.WriteLine("fn={0}", EntryPoint.Name);
            foreach (var axiom in TheProgram.TopLevelDeclarations.OfType<Axiom>())
                PrintCostLine(GetLineNumber(axiom), axiom.GetInstructionStatistics());

            TW.WriteLine("# End axioms");

            // FIXME: Walk up callgraph instead
            var printedImplementationsWithProcedures = new HashSet<Procedure>();
            foreach (var impl in TheProgram.TopLevelDeclarations.OfType<Implementation>())
            {
                Print(impl);
                printedImplementationsWithProcedures.Add(impl.Proc);
            }

            // Print Procedures that haven't been printed yet. This can happen when calling into a procedure instead of an implementation
            foreach (var proc in TheProgram.TopLevelDeclarations.OfType<Procedure>().Where( p => ! printedImplementationsWithProcedures.Contains(p)))
            {
                Print(proc);
            }
        }
    }
}

