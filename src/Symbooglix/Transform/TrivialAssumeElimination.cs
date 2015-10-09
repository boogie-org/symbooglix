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
using Microsoft.Boogie;
using System.Collections.Generic;

namespace Symbooglix
{
    namespace Transform
    {
        public class TrivialAssumeElimination : IPass
        {
            public TrivialAssumeElimination()
            {
            }

            public string GetName()
            {
                return "Trivial assume elimination";
            }

            public void SetPassInfo(ref PassInfo passInfo)
            {
                return;
            }

            public bool RunOn(Microsoft.Boogie.Program prog, PassInfo passInfo)
            {
                var blocks = prog.Blocks();
                bool changed = false;
                foreach (var block in blocks)
                {
                    var newCmds = new List<Cmd>();
                    foreach (var cmd in block.Cmds)
                    {
                        if (cmd is AssumeCmd)
                        {
                            var assumeCmd = cmd as AssumeCmd;
                            if (ExprUtil.IsTrue(assumeCmd.Expr))
                            {
                                // This is a trivial assume
                                Console.WriteLine("Removing trivial assume true on line {0}", assumeCmd.tok.line);
                                changed = true;
                                continue;
                            }
                        }
                        // Add the existing command to the list if we want to keep it
                        newCmds.Add(cmd);
                    }

                    if (block.cmds.Count > newCmds.Count)
                    {
                        // Assign new list if necessary
                        block.Cmds = newCmds;
                    }
                }
                return changed;
            }

            public void Reset()
            {
                // Nothing to do
            }
        }
    }
}

