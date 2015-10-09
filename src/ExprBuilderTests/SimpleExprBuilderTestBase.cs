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
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Linq;

using BPLType = Microsoft.Boogie.Type;

namespace ExprBuilderTests
{
    public class SimpleExprBuilderTestBase : IErrorSink
    {
        public SimpleExprBuilderTestBase()
        {
            // This is a hack
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();
        }

        public SimpleExprBuilder GetSimpleBuilder()
        {
            return new SimpleExprBuilder(/*immutable=*/ true);
        }

        public void Error(IToken tok, string msg)
        {
            Assert.Fail(msg);
        }

        protected void CheckBvBuiltIn(Expr e, string expected)
        {
            Assert.IsInstanceOf<NAryExpr>(e);
            var asNary = e as NAryExpr;
            Assert.IsInstanceOf<FunctionCall>(asNary.Fun);
            var fc = asNary.Fun as FunctionCall;
            var actual = QKeyValue.FindStringAttribute(fc.Func.Attributes, "bvbuiltin");
            Assert.IsNotNullOrEmpty(actual);
            Assert.AreEqual(expected, actual);
        }

        protected void CheckBuiltIn(Expr e, string expected)
        {
            Assert.IsInstanceOf<NAryExpr>(e);
            var asNary = e as NAryExpr;
            Assert.IsInstanceOf<FunctionCall>(asNary.Fun);
            var fc = asNary.Fun as FunctionCall;
            var actual = QKeyValue.FindStringAttribute(fc.Func.Attributes, "builtin");
            Assert.IsNotNullOrEmpty(actual);
            Assert.AreEqual(expected, actual);
        }

        protected void CheckIsBoolType(Expr result)
        {
            var shallowType = result.ShallowType;
            Assert.IsNotNull(shallowType);
            Assert.IsTrue(shallowType.IsBool);
            var t = result.Type;
            Assert.IsNotNull(t);
            Assert.IsTrue(t.IsBool);
            var TC = new TypecheckingContext(this);
            result.Typecheck(TC);
        }

        protected void CheckIsBvType(Expr result, int width)
        {
            var shallowType = result.ShallowType;
            Assert.IsNotNull(shallowType);
            Assert.IsTrue(shallowType.IsBv);
            Assert.AreEqual(width, shallowType.BvBits);
            var t = result.Type;
            Assert.IsNotNull(t);
            Assert.IsTrue(t.IsBv);
            Assert.AreEqual(width, t.BvBits);
            var TC = new TypecheckingContext(this);
            result.Typecheck(TC);
        }

        protected void CheckIsReal(Expr result)
        {
            Assert.IsTrue(result.ShallowType.IsReal);
            Assert.IsNotNull(result.Type);
            Assert.IsTrue(result.Type.IsReal);
            var TC = new TypecheckingContext(this);
            result.Typecheck(TC);
        }

        protected void CheckIsInt(Expr result)
        {
            Assert.IsTrue(result.ShallowType.IsInt);
            Assert.IsNotNull(result.Type);
            Assert.IsTrue(result.Type.IsInt);
            var TC = new TypecheckingContext(this);
            result.Typecheck(TC);
        }

        protected void CheckType(Expr e, Predicate<Microsoft.Boogie.Type> p)
        {
            Assert.IsNotNull(e.ShallowType);
            Assert.IsTrue(p(e.ShallowType));
            Assert.IsNotNull(e.Type);
            Assert.AreEqual(e.ShallowType, e.Type);
            var TC = new TypecheckingContext(this);
            e.Typecheck(TC);
        }

        protected void CheckIsMapType(Expr e, Microsoft.Boogie.Type mapsToType, params Microsoft.Boogie.Type[] indicesType)
        {
            Assert.IsNotNull(e.ShallowType);
            InternalCheckIsMapType(e.ShallowType, mapsToType, indicesType);
            Assert.IsNotNull(e.Type);
            InternalCheckIsMapType(e.Type, mapsToType, indicesType);
        }

        private void InternalCheckIsMapType(Microsoft.Boogie.Type theMapType, Microsoft.Boogie.Type mapsToType, params Microsoft.Boogie.Type[] indicesType)
        {
            Assert.IsTrue(theMapType.IsMap);
            Assert.AreEqual(mapsToType, theMapType.AsMap.Result);
            Assert.AreEqual(theMapType.MapArity, indicesType.Length);
            for (int index = 0; index < indicesType.Length; ++index)
            {
                Assert.AreEqual(theMapType.AsMap.Arguments[index], indicesType[index]);
            }
        }

        protected Tuple<IdentifierExpr, BPLType> GetMapVariable(string name, BPLType resultTyp, params BPLType[] indices)
        {
            var mapType = new MapType(Token.NoToken,
                new List<Microsoft.Boogie.TypeVariable>(),
                indices.ToList(),
                resultTyp);
            var typeIdent = new TypedIdent(Token.NoToken, name, mapType);
            var gv = new GlobalVariable(Token.NoToken, typeIdent);
            var id = new IdentifierExpr(Token.NoToken, gv, /*immutable=*/ true);

            var result = new Tuple<IdentifierExpr, BPLType>(id, mapType);
            return result;
        }

        protected Tuple<Variable, IdentifierExpr> GetVarAndIdExpr(string name, Microsoft.Boogie.Type type)
        {
            var typeIdent = new TypedIdent(Token.NoToken, name, type);
            var v = new GlobalVariable(Token.NoToken, typeIdent);
            var id = new IdentifierExpr(Token.NoToken, v, /*immutable=*/ true);
            return new Tuple<Variable, IdentifierExpr>(v, id);
        }

        protected Tuple<Variable, IdentifierExpr> GetBoundVarAndIdExpr(string name, Microsoft.Boogie.Type type)
        {
            var typeIdent = new TypedIdent(Token.NoToken, name, type);
            var v = new BoundVariable(Token.NoToken, typeIdent);
            var id = new IdentifierExpr(Token.NoToken, v, /*immutable=*/ true);
            return new Tuple<Variable, IdentifierExpr>(v, id);
        }


    }
}

