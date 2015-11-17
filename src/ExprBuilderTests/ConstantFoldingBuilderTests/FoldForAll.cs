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
using Microsoft.Boogie;
using System.Collections.Generic;
using Symbooglix;

using BPLType = Microsoft.Boogie.Type;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldForAll : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void TrueBody()
        {
            var cfb = GetConstantFoldingBuilder();
            var xPair = GetBoundVarAndIdExpr("x", BasicType.Int);
            var freeVarX = xPair.Item1;
            var x = xPair.Item2;
            var result = cfb.ForAll(new List<Variable>() {freeVarX}, cfb.True);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void FalseBody()
        {
            var cfb = GetConstantFoldingBuilder();
            var xPair = GetBoundVarAndIdExpr("x", BasicType.Int);
            var freeVarX = xPair.Item1;
            var x = xPair.Item2;
            var result = cfb.ForAll(new List<Variable>() {freeVarX}, cfb.False);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void NoFold()
        {
            var pair = GetSimpleAndConstantFoldingBuilder();
            var sb = pair.Item1;
            var cfb = pair.Item2;
            var xPair = GetBoundVarAndIdExpr("x", BasicType.Int);
            var freeVarX = xPair.Item1;
            var x = xPair.Item2;

            var yPair = GetBoundVarAndIdExpr("y", BasicType.Int);
            var freeVarY = yPair.Item1;
            var y = yPair.Item2;

            var fb = new FunctionCallBuilder();
            var dummyFunc = fb.CreateCachedUninterpretedFunctionCall("f", BPLType.Bool,
                new List<BPLType>() {BPLType.Int, BPLType.Int});

            var triggerExpr = sb.UFC(dummyFunc, x, y);
            var trigger = new Trigger(Token.NoToken,
                /*pos=*/true,
                new List<Expr>() { triggerExpr },
                null);

            var foldedResult = cfb.ForAll(new List<Variable>() { freeVarX, freeVarY}, cfb.Lt(x,y), trigger);
            var simpleResult = sb.ForAll(new List<Variable>() {freeVarX, freeVarY}, sb.Lt(x,y), trigger);
            CheckIsBoolType(foldedResult);
            CheckIsBoolType(simpleResult);
            Assert.AreEqual(simpleResult, foldedResult);

            // FIXME: Equals() currently doesn't check triggers, so do it manually
            Assert.IsInstanceOf<ForallExpr>(foldedResult);
            Assert.IsInstanceOf<ForallExpr>(simpleResult);
            var foldedResultAsForAll = foldedResult as ForallExpr;
            var simpleResultAsForAll = simpleResult as ForallExpr;
            Assert.IsNotNull(foldedResultAsForAll.Triggers);
            Assert.IsNull(foldedResultAsForAll.Triggers.Next);
            Assert.IsNotNull(simpleResultAsForAll.Triggers);
            Assert.IsNull(simpleResultAsForAll.Triggers.Next);
            Assert.AreSame(foldedResultAsForAll.Triggers, simpleResultAsForAll.Triggers);

            // Use this gross Boogie API too
            Assert.IsTrue(BinderExpr.EqualWithAttributesAndTriggers(simpleResult, foldedResult));
        }
    }
}

