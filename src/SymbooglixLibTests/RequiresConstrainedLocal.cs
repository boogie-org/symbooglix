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
using Microsoft.Boogie;
using Symbooglix;
using System.Linq;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class RequiresConstrainedLocal : SymbooglixTest
    {
        public RequiresConstrainedLocal()
        {
            SetupDebug();
            SetupCmdLineParser();
        }

        [Test()]
        public void NonRecursive()
        {
            p = LoadProgramFrom("programs/RequiresConstrainedLocal.bpl");
            e = GetExecutor(p);
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                // Find the "a" local variable
                var pair = e.CurrentState.GetInScopeVariableAndExprByName("a");
                Variable V = pair.Key;
                Expr E = pair.Value;

                Assert.IsTrue(E is IdentifierExpr);
                var id = E as IdentifierExpr;
                Assert.IsTrue(id.Decl is SymbolicVariable);

                // Check we have the expected constraint
                string expected = "BVUGT8(" + id.Name + ", 2bv8)";
                Assert.AreEqual(e.CurrentState.Constraints.Count, 1);
                Assert.IsTrue(e.CurrentState.Constraints.Constraints.Where( c => c.Condition.ToString() == expected).Count() == 1);
            };
            e.Run(GetMain(p));
        }
    }
}

