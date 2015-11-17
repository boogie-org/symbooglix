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
using Symbooglix;
using NUnit.Framework;
using Microsoft.Boogie;
using System.Collections.Generic;

using BPLType = Microsoft.Boogie.Type;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class QuantifiersSimpleBuilder : SimpleExprBuilderTestBase
    {
        // FIXME: Use GetVarAndIdExpr instead
        private Variable GetVariable(string name, Microsoft.Boogie.Type type)
        {
            var typedIdent = new TypedIdent(Token.NoToken, name, type);
            var gv = new GlobalVariable(Token.NoToken, typedIdent);
            return gv;
        }

        [Test()]
        public void SimpleForAll()
        {
            var builder = GetSimpleBuilder();
            var freeVarX = GetVariable("x", BasicType.Int);
            var xid = new IdentifierExpr(Token.NoToken, freeVarX);
            var freeVarY = GetVariable("y", BasicType.Int);
            var yid = new IdentifierExpr(Token.NoToken, freeVarY);
            var body = builder.Eq(xid, yid);
            var result = builder.ForAll(new List<Variable>() { freeVarX, freeVarY }, body);
            Assert.AreEqual("(forall x: int, y: int :: x == y)", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void SimpleForAllWithTrigger()
        {
            var builder = GetSimpleBuilder();
            var freeVarX = GetVariable("x", BasicType.Int);
            var xid = new IdentifierExpr(Token.NoToken, freeVarX);

            var fb = new FunctionCallBuilder();
            var funcCall = fb.CreateUninterpretedFunctionCall("f", BPLType.Int, new List<BPLType>() { BPLType.Int });
            var body = builder.Gt(builder.UFC(funcCall, xid), xid);

            // Single trigger
            var triggers = new Microsoft.Boogie.Trigger(Token.NoToken,
                                                       /*positive=*/true,
                                                       new List<Expr>() { builder.UFC(funcCall, xid) }, null);

            var result = builder.ForAll(new List<Variable>() { freeVarX}, body, triggers);
            Assert.AreEqual("(forall x: int :: { f(x) } f(x) > x)", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SimpleForAllWrongBodyType()
        {
            var builder = GetSimpleBuilder();
            var freeVarX = GetVariable("x", BasicType.Int);
            var xid = new IdentifierExpr(Token.NoToken, freeVarX);
            var freeVarY = GetVariable("y", BasicType.Int);
            var yid = new IdentifierExpr(Token.NoToken, freeVarY);
            var body = builder.Add(xid, yid); // Wrong body type, should be bool
            builder.ForAll(new List<Variable>() { freeVarX, freeVarY }, body);
        }

        [Test()]
        public void SimpleExists()
        {
            var builder = GetSimpleBuilder();
            var freeVarX = GetVariable("x", BasicType.Int);
            var xid = new IdentifierExpr(Token.NoToken, freeVarX);
            var freeVarY = GetVariable("y", BasicType.Int);
            var yid = new IdentifierExpr(Token.NoToken, freeVarY);
            var body = builder.Eq(xid, yid);
            var result = builder.Exists(new List<Variable>() { freeVarX, freeVarY }, body);
            Assert.AreEqual("(exists x: int, y: int :: x == y)", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void SimpleExistsWithTrigger()
        {
            var builder = GetSimpleBuilder();
            var freeVarX = GetVariable("x", BasicType.Int);
            var xid = new IdentifierExpr(Token.NoToken, freeVarX);

            var fb = new FunctionCallBuilder();
            var funcCall = fb.CreateUninterpretedFunctionCall("f", BPLType.Int, new List<BPLType>() { BPLType.Int });
            var body = builder.Gt(builder.UFC(funcCall, xid), xid);

            // Single trigger
            var triggers = new Microsoft.Boogie.Trigger(Token.NoToken,
                /*positive=*/true,
                new List<Expr>() { builder.UFC(funcCall, xid) }, null);

            var result = builder.Exists(new List<Variable>() { freeVarX}, body, triggers);
            Assert.AreEqual("(exists x: int :: { f(x) } f(x) > x)", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SimpleExistsAllWrongBodyType()
        {
            var builder = GetSimpleBuilder();
            var freeVarX = GetVariable("x", BasicType.Int);
            var xid = new IdentifierExpr(Token.NoToken, freeVarX);
            var freeVarY = GetVariable("y", BasicType.Int);
            var yid = new IdentifierExpr(Token.NoToken, freeVarY);
            var body = builder.Add(xid, yid); // Wrong body type, should be bool
            builder.Exists(new List<Variable>() { freeVarX, freeVarY }, body);
        }
    }
}

