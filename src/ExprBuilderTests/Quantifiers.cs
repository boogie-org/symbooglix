﻿using System;
using Symbooglix;
using NUnit.Framework;
using Microsoft.Boogie;
using System.Collections.Generic;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class Quantifiers
    {
        public Quantifiers ()
        {
            // This is a hack
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();
        }

        private IExprBuilder GetBuilder()
        {
            return new SimpleExprBuilder();
        }

        private Variable GetVariable(string name, Microsoft.Boogie.Type type)
        {
            var typedIdent = new TypedIdent(Token.NoToken, name, type);
            var gv = new GlobalVariable(Token.NoToken, typedIdent);
            return gv;
        }

        [Test()]
        public void SimpleForAll()
        {
            var builder = GetBuilder();
            var freeVarX = GetVariable("x", BasicType.Int);
            var xid = new IdentifierExpr(Token.NoToken, freeVarX);
            var freeVarY = GetVariable("y", BasicType.Int);
            var yid = new IdentifierExpr(Token.NoToken, freeVarY);
            var body = builder.Eq(xid, yid);
            var result = builder.ForAllExpr(new List<Variable>() { freeVarX, freeVarY }, body);
            Assert.AreEqual("(forall x: int, y: int :: x == y)", result.ToString());
            Assert.AreEqual(BasicType.Bool, result.ShallowType);
            Assert.IsNotNull(result.Type);
            Assert.AreEqual(BasicType.Bool, result.Type);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SimpleForAllWrongBodyType()
        {
            var builder = GetBuilder();
            var freeVarX = GetVariable("x", BasicType.Int);
            var xid = new IdentifierExpr(Token.NoToken, freeVarX);
            var freeVarY = GetVariable("y", BasicType.Int);
            var yid = new IdentifierExpr(Token.NoToken, freeVarY);
            var body = builder.Add(xid, yid); // Wrong body type, should be bool
            builder.ForAllExpr(new List<Variable>() { freeVarX, freeVarY }, body);
        }
    }
}
