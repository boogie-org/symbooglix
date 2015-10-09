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
using System.Diagnostics;
using System.Linq;

namespace Symbooglix
{
    namespace Transform
    {
        /// <summary>
        /// Axiom and entry requires check transform pass.
        ///
        /// This pass transforms the program by removing all procedures
        /// apart from the entry points and then replaces all entry point
        /// bodies with "assert false". The program can then be checked
        /// by a tool like Boogie or Corral. If no bug is found it implies
        /// the axioms and/or requires are inconsistent in some way
        /// </summary>
        public class AxiomAndEntryRequiresCheckTransformPass : IPass
        {
            public readonly Predicate<Implementation> IsEntryPoint;
            public AxiomAndEntryRequiresCheckTransformPass(Predicate<Implementation> isEntryPoint)
            {
                IsEntryPoint = isEntryPoint;
            }

            public string GetName()
            {
                return "Axiom and entry requires check Transform";
            }

            public void SetPassInfo(ref PassInfo passInfo)
            {
                return;
            }

            public bool RunOn(Microsoft.Boogie.Program prog, PassInfo passInfo)
            {
                var toRemove = new HashSet<Declaration>();
                var implToFalsify = new List<Implementation>();
                var procToKeep = new HashSet<Declaration>();

                // Check there is at least one entry point
                bool containsEntryPoint = false;
                foreach (var impl in prog.TopLevelDeclarations.OfType<Implementation>())
                {
                    if (IsEntryPoint(impl))
                    {
                        containsEntryPoint = true;
                        break;
                    }
                }

                if (!containsEntryPoint)
                    throw new EntryPointNotFoundException();

                // Determine which implementation we want to remove and
                // which implementations we will need to keep
                foreach (var decl in prog.TopLevelDeclarations)
                {
                    var declAsImplementation = decl as Implementation;
                    if (declAsImplementation == null)
                        continue;

                    if (!IsEntryPoint(declAsImplementation))
                    {
                        // We want to remove this implementation
                        toRemove.Add(declAsImplementation);
                    }
                    else
                    {
                        implToFalsify.Add(declAsImplementation);
                        Debug.Assert(declAsImplementation.Proc != null);
                        procToKeep.Add(declAsImplementation.Proc);
                    }
                }

                // Determine which procedures we should remove
                foreach (var decl in prog.TopLevelDeclarations)
                {
                    var declAsProc = decl as Procedure;
                    if (declAsProc == null)
                        continue;

                    if (!procToKeep.Contains(declAsProc))
                        toRemove.Add(declAsProc);
                }

                // Now remove the procedures and implementations we don't need
                foreach (var decl in toRemove)
                {
                    prog.RemoveTopLevelDeclaration(decl);
                }

                // Now change entry point bodies to just contain an "assert false"
                foreach (var impl in implToFalsify)
                {
                    // Remove any ensures. We probably aren't maintaining it
                    // any more if we remove the body.
                    impl.Proc.Ensures.Clear();

                    // The body won't be modifying anything so clear the modset
                    impl.Proc.Modifies.Clear();

                    // Remove existing blocks
                    impl.Blocks.Clear();

                    // Add block that asserts false and then returns
                    var newBlock = new Block(Token.NoToken,
                                             "entry",
                                             new List<Cmd>() { new AssertCmd(Token.NoToken, Expr.False) },
                                             new ReturnCmd(Token.NoToken));
                    impl.Blocks.Add(newBlock);
                }

                return ( toRemove.Count + implToFalsify.Count ) > 0;
            }

            public void Reset()
            {
                return;
            }
        }

        class NoEntryPointFoundException : Exception
        {

        }
    }
}

