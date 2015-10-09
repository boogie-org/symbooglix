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
using NUnit.Framework;
using Symbooglix;
using System.Linq;
using Microsoft.Boogie;
using System.Collections.Generic;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class CachingSymbolicPoolTests
    {

        public CachingSymbolicPoolTests()
        {
            // HACK:
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
        }

        private ExecutionState MkExecutionState()
        {
            return new ExecutionState();
        }

        [TestCase(), Ignore("Design is broken. It needs rethinking")]
        public void variableCache()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
            procedure main()
            {
                var x:int;
                var y:int;
                return;
            }
            ", "test.bpl");

            // The Program needs to be annotated with ProgramLocations for this test to work
            var PM = new Symbooglix.Transform.PassManager();
            PM.Add(new Symbooglix.Annotation.ProgramLocationAnnotater());
            PM.Run(prog);

            var pool = new CachingSymbolicPool();

            // Get the Variables we will request SymbolicVariables for
            var mainImpl = prog.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First();
            var xVar = mainImpl.LocVars[0];
            var yVar = mainImpl.LocVars[1];

            // Make a few ExecutionStates. We don't need to do anything with them, we are effectively using
            // them as a key into our data structure
            var state0 = MkExecutionState();
            var state1 = state0.Clone(xVar.GetProgramLocation()); // HACK: Just use any old program location
            var state2 = state1.Clone(xVar.GetProgramLocation());

            var xSyms = new List<SymbolicVariable>();
            var ySyms = new List<SymbolicVariable>();

            xSyms.Add(pool.GetFreshSymbolic(xVar, state0));
            ySyms.Add(pool.GetFreshSymbolic(yVar, state0));

            xSyms.Add(pool.GetFreshSymbolic(xVar, state1));
            xSyms.Add(pool.GetFreshSymbolic(xVar, state2));
            ySyms.Add(pool.GetFreshSymbolic(yVar, state1));
            ySyms.Add(pool.GetFreshSymbolic(yVar, state2));

            // Now check we only ever got two instances

            foreach (var sym in xSyms)
            {
                Assert.IsNotNull(sym);
                Assert.AreSame(xSyms[0], sym);
            }

            foreach (var sym in ySyms)
            {
                Assert.IsNotNull(sym);
                Assert.AreSame(ySyms[0], sym);
            }

            // Now State1 will ask for a new symbolic so it should get something new
            var xSymFirst = xSyms[0];
            xSyms.Clear();
            xSyms.Add(pool.GetFreshSymbolic(xVar, state1));
            xSyms.Add(pool.GetFreshSymbolic(xVar, state0));
            xSyms.Add(pool.GetFreshSymbolic(xVar, state2));

            Assert.AreNotSame(xSymFirst, xSyms[0]);

            foreach (var sym in xSyms)
            {
                Assert.IsNotNull(sym);
                Assert.AreSame(xSyms[0], sym);
            }

            // Create a new state it should not get xSymFirst because even though it has never asked for a symbolic before
            // the cache should be aware it is a child of state 1 which has already been given "xSymFirst".
            var state3 = state1.Clone(xVar.GetProgramLocation());
            var state3Request = pool.GetFreshSymbolic(xVar, state3);
            Assert.AreNotSame(xSymFirst, state3Request);

        }

        [TestCase(), Ignore("Design is broken. It needs rethinking")]
        public void HavocCache()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
            procedure main()
            {
                var x:int;
                var y:int;
                havoc x, y;
                return;
            }
            ", "test.bpl");

            // The Program needs to be annotated with ProgramLocations for this test to work
            var PM = new Symbooglix.Transform.PassManager();
            PM.Add(new Symbooglix.Annotation.ProgramLocationAnnotater());
            PM.Run(prog);

            var pool = new CachingSymbolicPool();

            var havocCmd = prog.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First().Blocks[0].Cmds[0] as HavocCmd;
            Assert.IsInstanceOf<HavocCmd>(havocCmd);

            // Make a few ExecutionStates. We don't need to do anything with them, we are effectively using
            // them as a key into our data structure
            var state0 = MkExecutionState();
            var state1 = state0.Clone(havocCmd.GetProgramLocation()); // HACK: Just use any old program location
            var state2 = state1.Clone(havocCmd.GetProgramLocation());

            var xHavocVars = new List<SymbolicVariable>();
            var yHavocVars = new List<SymbolicVariable>();

            xHavocVars.Add(pool.GetFreshSymbolic(havocCmd, 0, state0));
            xHavocVars.Add(pool.GetFreshSymbolic(havocCmd, 0, state1));
            xHavocVars.Add(pool.GetFreshSymbolic(havocCmd, 0, state2));

            yHavocVars.Add(pool.GetFreshSymbolic(havocCmd, 1, state0));
            yHavocVars.Add(pool.GetFreshSymbolic(havocCmd, 1, state1));
            yHavocVars.Add(pool.GetFreshSymbolic(havocCmd, 1, state2));


            // Now check we only ever got two instances

            foreach (var sym in xHavocVars)
            {
                Assert.IsNotNull(sym);
                Assert.AreSame(xHavocVars[0], sym);
            }

            foreach (var sym in yHavocVars)
            {
                Assert.IsNotNull(sym);
                Assert.AreSame(yHavocVars[0], sym);
            }

            // Now State1 will ask for a new symbolic so it should get something new
            var xSymFirst = xHavocVars[0];
            xHavocVars.Clear();
            xHavocVars.Add(pool.GetFreshSymbolic(havocCmd, 0, state1));
            xHavocVars.Add(pool.GetFreshSymbolic(havocCmd, 0, state0));
            xHavocVars.Add(pool.GetFreshSymbolic(havocCmd, 0, state2));

            Assert.AreNotSame(xSymFirst, xHavocVars[0]);

            foreach (var sym in xHavocVars)
            {
                Assert.IsNotNull(sym);
                Assert.AreSame(xHavocVars[0], sym);
            }

            // Create a new state it should not get xSymFirst because even though it has never asked for a symbolic before
            // the cache should be aware it is a child of state 1 which has already been given "xSymFirst".
            var state3 = state1.Clone(havocCmd.GetProgramLocation());
            var state3Request = pool.GetFreshSymbolic(havocCmd, 0, state3);
            Assert.AreNotSame(xSymFirst, state3Request);
        }

        [TestCase(), Ignore("Design is broken. It needs rethinking")]
        public void ModsetCache()
        {
            var prog = SymbooglixLibTests.SymbooglixTest.LoadProgramFrom(@"
            var g:int;
            var h:int;
            procedure main()
            modifies g, h;
            {
                g := 0;
                return;
            }
            ", "test.bpl");

            // The Program needs to be annotated with ProgramLocations for this test to work
            var PM = new Symbooglix.Transform.PassManager();
            PM.Add(new Symbooglix.Annotation.ProgramLocationAnnotater());
            PM.Run(prog);

            var pool = new CachingSymbolicPool();

            var proc = prog.TopLevelDeclarations.OfType<Procedure>().Where(p => p.Name == "main").First();

            // Make a few ExecutionStates. We don't need to do anything with them, we are effectively using
            // them as a key into our data structure
            var state0 = MkExecutionState();
            var state1 = state0.Clone(proc.GetModSetProgramLocation()); // HACK: Just use any old program location
            var state2 = state1.Clone(proc.GetModSetProgramLocation());


            var gVars = new List<SymbolicVariable>();
            var hVars = new List<SymbolicVariable>();

            gVars.Add(pool.GetFreshSymbolic(proc, 0, state0));
            gVars.Add(pool.GetFreshSymbolic(proc, 0, state1));
            gVars.Add(pool.GetFreshSymbolic(proc, 0, state2));

            hVars.Add(pool.GetFreshSymbolic(proc, 1, state0));
            hVars.Add(pool.GetFreshSymbolic(proc, 1, state1));
            hVars.Add(pool.GetFreshSymbolic(proc, 1, state2));

            foreach (var sym in gVars)
            {
                Assert.IsNotNull(sym);
                Assert.AreSame(gVars[0], sym);
            }

            foreach (var sym in hVars)
            {
                Assert.IsNotNull(sym);
                Assert.AreSame(hVars[0], sym);
            }

            // Now State1 will ask for a new symbolic so it should get something new
            var gSymFirst = gVars[0];
            gVars.Clear();
            gVars.Add(pool.GetFreshSymbolic(proc, 0, state1));
            gVars.Add(pool.GetFreshSymbolic(proc, 0, state0));
            gVars.Add(pool.GetFreshSymbolic(proc, 0, state2));

            Assert.AreNotSame(gSymFirst, gVars[0]);

            foreach (var sym in gVars)
            {
                Assert.IsNotNull(sym);
                Assert.AreSame(gVars[0], sym);
            }

            // Create a new state it should not get gSymFirst because even though it has never asked for a symbolic before
            // the cache should be aware it is a child of state 1 which has already been given "xSymFirst".
            var state3 = state1.Clone(proc.GetModSetProgramLocation()); // HACK: Use any old program location
            var state3Request = pool.GetFreshSymbolic(proc, 0, state3);
            Assert.AreNotSame(gSymFirst, state3Request);

        }
    }
}

