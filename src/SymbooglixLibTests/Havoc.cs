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
using NUnit.Framework;
using Microsoft.Boogie;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Havoc : SymbooglixTest
    {
        [Test()]
        public void simpleHavoc()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var a:int;
                    a := 1;
                    assert {:symbooglix_bp ""a_is_concrete""} true;
                    havoc a;
                    assert {:symbooglix_bp ""a_is_symbolic""} true;
                }

                ", "test.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            int counter = 0;
            KeyValuePair<Variable,Expr>? aBefore = null;
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArgs)
            {
                switch (eventArgs.Name)
                {
                    case "a_is_concrete":
                        aBefore = e.CurrentState.GetInScopeVariableAndExprByName("a");
                        var asLit = ExprUtil.AsLiteral(aBefore.Value.Value);
                        Assert.IsNotNull(asLit);
                        Assert.IsTrue(asLit.isBigNum);
                        Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(1), asLit.asBigNum);
                        break;
                    case "a_is_symbolic":
                        var aAfter = e.CurrentState.GetInScopeVariableAndExprByName("a");
                        Assert.IsTrue(aBefore != null && aBefore.HasValue);
                        Assert.AreNotSame(aBefore.Value, aAfter.Value);
                        var asId = ExprUtil.AsIdentifer(aAfter.Value);
                        Assert.IsNotNull(asId);
                        break;
                    default:
                        Assert.Fail("Unrecognised breakpoint");
                        break;
                }
                ++counter;
            };

            e.Run(GetMain(p));
            Assert.AreEqual(2, counter);
        }
    }
}

