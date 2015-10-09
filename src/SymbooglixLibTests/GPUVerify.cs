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

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class GPUVerify : SymbooglixTest
    {
        [Test()]
        public void AssignmentOfConcreteValuesFromAxioms()
        {
            p = LoadProgramFrom("programs/GPUVerifyAxiomAssignmentTest.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver(), /*useConstantFolding=*/ true);

            int counter = 0;

            var group_size_x = p.TopLevelDeclarations.OfType<Variable>().Where(v => v.Name == "group_size_x").First();
            var group_size_y = p.TopLevelDeclarations.OfType<Variable>().Where(v => v.Name == "group_size_y").First();
            var group_size_z = p.TopLevelDeclarations.OfType<Variable>().Where(v => v.Name == "group_size_z").First();

            var num_groups_x = p.TopLevelDeclarations.OfType<Variable>().Where(v => v.Name == "num_groups_x").First();
            var num_groups_y = p.TopLevelDeclarations.OfType<Variable>().Where(v => v.Name == "num_groups_y").First();
            var num_groups_z = p.TopLevelDeclarations.OfType<Variable>().Where(v => v.Name == "num_groups_z").First();

            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArg)
            {
                ++counter;
                Assert.AreEqual("check", eventArg.Name);

                // Check the Constants are assigned as expected
                Assert.AreEqual("512bv32",e.CurrentState.GetGlobalVariableExpr(group_size_x).ToString());
                Assert.AreEqual("1bv32",e.CurrentState.GetGlobalVariableExpr(group_size_y).ToString());
                Assert.AreEqual("1bv32",e.CurrentState.GetGlobalVariableExpr(group_size_z).ToString());

                Assert.AreEqual("256bv32",e.CurrentState.GetGlobalVariableExpr(num_groups_x).ToString());
                Assert.AreEqual("1bv32",e.CurrentState.GetGlobalVariableExpr(num_groups_y).ToString());
                Assert.AreEqual("1bv32",e.CurrentState.GetGlobalVariableExpr(num_groups_z).ToString());
            };

            var tc = new TerminationCounter();
            tc.Connect(e);

            e.Run(GetMain(p));
            Assert.AreEqual(1, counter);
            Assert.AreEqual(1, tc.Sucesses);
            Assert.AreEqual(1, tc.NumberOfTerminatedStates);
        }
    }
}

