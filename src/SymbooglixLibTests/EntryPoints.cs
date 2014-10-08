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
            p = loadProgram("programs/InstructionStatistics.bpl");
            e = getExecutor(p, new DFSStateScheduler(), GetSolver());

            var main = getMain(p);
            var foo = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "foo").First();

            e.Run(main);
            e.Run(foo);

            Assert.AreEqual(2, e.RequestedEntryPoints.Count());

            var expectedList = new List<Implementation>() { main, foo };

            foreach (var pair in expectedList.Zip( e.RequestedEntryPoints))
                Assert.AreSame(pair.Item1, pair.Item2);
        }
    }
}

