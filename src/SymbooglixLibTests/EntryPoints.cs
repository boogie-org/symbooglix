//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using NUnit.Framework;
using System;
using Symbooglix;
using System.Linq;
using Microsoft.Boogie;
using System.Collections.Generic;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class EntryPoints : SymbooglixTest
    {
        [Test()]
        public void RecordedEntryPoints()
        {
            p = LoadProgramFrom("programs/InstructionStatistics.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var main = GetMain(p);
            var foo = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "foo").First();

            e.Run(main);
            e.Run(foo);

            Assert.AreEqual(2, e.RequestedEntryPoints.Count());

            var expectedList = new List<Implementation>() { main, foo };

            foreach (var pair in expectedList.Zip( e.RequestedEntryPoints))
                Assert.AreSame(pair.Item1, pair.Item2);
        }

        [Test()]
        public void RecordEntryPointEarly()
        {
            p = LoadProgramFrom("programs/InconsistentAxioms.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var main = GetMain(p);

            var counter = new TerminationCounter();
            counter.Connect(e);

            try
            {
                e.Run(main);
            }
            catch (InitialStateTerminated)
            {
                // Ignore
            }

            Assert.AreEqual(1, counter.UnsatisfiableAxioms);

            Assert.AreEqual(1, e.RequestedEntryPoints.Count());
            Assert.AreSame(main, e.RequestedEntryPoints.First());
        }
    }
}

