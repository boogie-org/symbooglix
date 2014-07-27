using Microsoft.Boogie;
using NUnit.Framework;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;


namespace BoogieTests
{
    [TestFixture()]
    public class MissingStdDispatchInAbsyNode
    {
        private Program TheProgram;

        public MissingStdDispatchInAbsyNode()
        {
            // Necessary because we want to hit a Debug.Assert() failure in Boogie
            BoogieTest.setupDebug();
            BoogieTest.setupCmdLineParser();
            TheProgram = BoogieTest.loadProgram("programs/requires_ensures.bpl");
        }

        [Test()]
        public void VisitRequires()
        {
            var requires = TheProgram.TopLevelDeclarations.OfType<Procedure>().SelectMany(p => p.Requires);
            Assert.AreEqual(1, requires.Count());

            var visitor = new DoNothingVisitor();

            // A Buggy version of Boogie hits a Debug.Assert() failure in here
            // Because Requires is missing its StdDispatch() method
            visitor.Visit(requires.First());
        }

        [Test()]
        public void VisitEnsures()
        {
            var ensures = TheProgram.TopLevelDeclarations.OfType<Procedure>().SelectMany(p => p.Ensures);
            Assert.AreEqual(1, ensures.Count());

            var visitor = new DoNothingVisitor();
            // A Buggy version of Boogie hits a Debug.Assert() failure in here
            // Because Ensures is missing its StdDispatch() method
            visitor.Visit(ensures.First());
        }

        class DoNothingVisitor : ReadOnlyVisitor
        {

        }
    }
}

