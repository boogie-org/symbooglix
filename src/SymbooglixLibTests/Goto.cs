//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using Microsoft.Boogie;
using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Goto : SymbooglixTest
    {
        [Test()]
        public void SingleTarget()
        {
            int hits = 0;
            p = LoadProgramFrom("programs/GotoSinglePath.bpl");
            e = GetExecutor(p);
            //var handler = new SingleTargetHandler();
            //e.RegisterBreakPointHandler(handler);
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name == "entry")
                {
                    // FIXME: This is fragile, find a way to name the entry block
                    Assert.AreEqual("anon0", e.CurrentState.GetCurrentStackFrame().CurrentBlock.Label);
                    ++hits;
                }
                else if (data.Name == "reached")
                {
                    Assert.AreEqual("NEXT", e.CurrentState.GetCurrentStackFrame().CurrentBlock.Label);
                    ++hits;
                }
                else
                {
                    Assert.Fail("Unexpected break point");
                }
            };
            e.Run(GetMain(p));
            Assert.AreEqual(2, hits);

        }

        [Test()]
        public void MultipleTargets()
        {
            int hits = 0;
            p = LoadProgramFrom("programs/GotoMultiplePaths.bpl");
            e = GetExecutor(p);
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name == "entry")
                {
                    Assert.AreEqual("entry_block", e.CurrentState.GetCurrentStackFrame().CurrentBlock.Label);
                    ++hits;
                }
                else if (data.Name == "path0")
                {
                    Assert.AreEqual("P0", e.CurrentState.GetCurrentStackFrame().CurrentBlock.Label);
                    ++hits;

                    var a = e.CurrentState.GetInScopeVariableAndExprByName("a");
                    BvConst aBV = GetBVFromLiteral(a.Value as LiteralExpr);
                    Assert.AreEqual(7, aBV.Value.ToInt);
                }
                else if (data.Name == "path1")
                {
                    var a = e.CurrentState.GetInScopeVariableAndExprByName("a");
                    Assert.AreEqual("P1", e.CurrentState.GetCurrentStackFrame().CurrentBlock.Label);
                    BvConst aBV = GetBVFromLiteral(a.Value as LiteralExpr);
                    Assert.AreEqual(8, aBV.Value.ToInt);
                    ++hits;
                }
                else if (data.Name == "path2")
                {
                    var a = e.CurrentState.GetInScopeVariableAndExprByName("a");
                    Assert.AreEqual("P2", e.CurrentState.GetCurrentStackFrame().CurrentBlock.Label);
                    BvConst aBV = GetBVFromLiteral(a.Value as LiteralExpr);
                    Assert.AreEqual(9, aBV.Value.ToInt);
                    ++hits;
                }
                else
                {
                    Assert.Fail("Unexpected break point");
                }
            };
            e.Run(GetMain(p));
            Assert.AreEqual(4, hits);
        }
    }
}

