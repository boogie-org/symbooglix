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
using System.Linq;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class VariableStoreTests
    {
        protected virtual IVariableStore GetVariableStore()
        {
            return new SimpleVariableStore();
        }

        public Variable MkSimpleVar(string name, BPLType type)
        {
            return new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, name, type));
        }

        // FIXME: This copied from the ExprBuilder tests. Refactor this
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

        public IExprBuilder GetExprBuilder()
        {
            return new SimpleExprBuilder(/*immutable*/ true);
        }

        private void ValidateStore(IVariableStore store, Dictionary<Variable, Expr> expected)
        {
            Assert.AreEqual(expected.Count, store.Count);

            int keysCount = 0;
            foreach (var v in store.Keys)
            {
                ++keysCount;
                Assert.IsTrue(expected.ContainsKey(v));
                Assert.IsTrue(store.ContainsKey(v));
            }
            Assert.AreEqual(expected.Count, keysCount);

            // Dummy var
            var dummyVar = MkSimpleVar("dummy", BPLType.Bool);
            Assert.IsFalse(store.ContainsKey(dummyVar));

            int pairsCount = 0;
            foreach (var pair in store)
            {
                ++pairsCount;
                Assert.IsTrue(expected.ContainsKey(pair.Key));
                Assert.AreSame(expected[pair.Key], pair.Value);
            }
            Assert.AreEqual(expected.Count, pairsCount);
        }

        [Test()]
        public void AddSimpleVarsAndClone()
        {
            var store = GetVariableStore();
            var builder = GetExprBuilder();

            var expected = new Dictionary<Variable, Expr>();
            var g = MkSimpleVar("g", Microsoft.Boogie.Type.Bool);
            var h = MkSimpleVar("h", Microsoft.Boogie.Type.Int);
            var initialGValue = builder.True;
            var initialHValue = builder.ConstantInt(5);

            ValidateStore(store, expected);

            store.Add(g, initialGValue);
            expected[g] = initialGValue;
            ValidateStore(store, expected);

            store.Add(h, initialHValue);
            expected[h] = initialHValue;
            ValidateStore(store, expected);

            // clone
            var newStore = store.Clone();
            ValidateStore(newStore, expected);

            var newExpected = new Dictionary<Variable, Expr>(expected);

            // Modify the original store
            var newValueForOldg = builder.False;
            store[g] = newValueForOldg;
            expected[g] = newValueForOldg;
            ValidateStore(store, expected);

            // Make sure clone isn't modified
            ValidateStore(newStore, newExpected);
            // Just to be sure
            Assert.AreSame(initialGValue, newStore[g]);
            Assert.AreSame(newValueForOldg, store[g]);

            // Now modify the clone and make sure the original is not affected
            var newValueForH = builder.Add(builder.ConstantInt(5), builder.Identifier(h));
            newStore[h] = newValueForH;
            newExpected[h] = newValueForH;
            ValidateStore(newStore, newExpected);
            ValidateStore(store, expected);

            // Just to be sure
            Assert.AreSame(newValueForH, newStore[h]);
            Assert.AreSame(initialHValue, store[h]);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void InsertWrongType()
        {
            var store = GetVariableStore();
            var builder = GetExprBuilder();
            var g = MkSimpleVar("g", Microsoft.Boogie.Type.Bool);
            store.Add(g, builder.ConstantInt(5));
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void ModifyWrongType()
        {
            var store = GetVariableStore();
            var builder = GetExprBuilder();
            var g = MkSimpleVar("g", Microsoft.Boogie.Type.Bool);
            store.Add(g, builder.True);

            // Wrong type write
            store[g] = builder.ConstantInt(0);
        }

        [Test(), ExpectedException(typeof(System.ArgumentException))]
        public void ReinsertVariable()
        {
            var store = GetVariableStore();
            var builder = GetExprBuilder();
            var g = MkSimpleVar("g", Microsoft.Boogie.Type.Bool);
            store.Add(g, builder.True);

            // Trying to add again should fail
            store.Add(g, builder.False);
        }

        [Test()]
        public void AddSimpleAndMapVarsAndClone()
        {
            var store = GetVariableStore();
            var builder = GetExprBuilder();

            var expected = new Dictionary<Variable, Expr>();
            var g = MkSimpleVar("g", Microsoft.Boogie.Type.Bool);
            var h = MkSimpleVar("h", Microsoft.Boogie.Type.Int);
            var m = GetMapVariable("map", BPLType.Bool, BPLType.Int).Item1.Decl; // var map:[int]bool;


            var initialGValue = builder.True;
            var initialHValue = builder.ConstantInt(5);
            var initialMValue = GetMapVariable("dummy", BPLType.Bool, BPLType.Int).Item1;

            ValidateStore(store, expected);

            store.Add(g, initialGValue);
            expected[g] = initialGValue;
            ValidateStore(store, expected);

            store.Add(h, initialHValue);
            expected[h] = initialHValue;
            ValidateStore(store, expected);

            store.Add(m, initialMValue);
            expected[m] = initialMValue;
            ValidateStore(store, expected);

            // clone
            var newStore = store.Clone();
            ValidateStore(newStore, expected);

            var newExpected = new Dictionary<Variable, Expr>(expected);

            // Modify the original store
            var newValueForOldg = builder.False;
            store[g] = newValueForOldg;
            expected[g] = newValueForOldg;
            ValidateStore(store, expected);

            // Make sure clone isn't modified
            ValidateStore(newStore, newExpected);
            // Just to be sure
            Assert.AreSame(initialGValue, newStore[g]);
            Assert.AreSame(newValueForOldg, store[g]);

            // Now modify the clone and make sure the original is not affected
            var newValueForH = builder.Add(builder.ConstantInt(5), builder.Identifier(h));
            newStore[h] = newValueForH;
            newExpected[h] = newValueForH;
            ValidateStore(newStore, newExpected);
            ValidateStore(store, expected);

            // Just to be sure
            Assert.AreSame(newValueForH, newStore[h]);
            Assert.AreSame(initialHValue, store[h]);

            // Modify the map
            var newValueForM = builder.MapStore(initialMValue, builder.False, builder.ConstantInt(2));
            newStore[m] = newValueForM;
            newExpected[m] = newValueForM;
            ValidateStore(newStore, newExpected);
            ValidateStore(store, expected);

            // Just to be sure
            Assert.AreSame(newValueForM, newStore[m]);
            Assert.AreSame(initialMValue, store[m]);
        }
    }
}

