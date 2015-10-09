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
using BPLType = Microsoft.Boogie.Type;
using System.Linq;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class MapProxyTests
    {
        public MapProxyTests()
        {
            // HACK:
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
        }

        protected BPLType GetMapVariable(BPLType resultTyp, params BPLType[] indices)
        {
            var mapType = new MapType(Token.NoToken,
                new List<Microsoft.Boogie.TypeVariable>(),
                indices.ToList(),
                resultTyp);

            return mapType;
        }

        protected MapProxy GetMapProxy(Expr initialValue)
        {
            return new MapProxy(initialValue, 0);
        }

        // FIXME: move somewhere central
        public static Variable GetVariable(string name, BPLType type)
        {
            var v = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, name, type));
            return v;
        }

        public IExprBuilder GetSimpleExprBuilder()
        {
            return new SimpleExprBuilder(/*immutable=*/true);
        }

        [Test()]
        public void SymbolicWriteForcesStoresToBeDropped()
        {
            // Build var m:[int]bool;
            var mapTy = GetMapVariable(BPLType.Int, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", mapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            // m[0] := false
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(0) }, builder.ConstantInt(99));

            // m[2] := true
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(2) }, builder.ConstantInt(101));

            // m[5] := false
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(5) }, builder.ConstantInt(25));

            // Read back
            Assert.AreEqual(builder.ConstantInt(99), mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));
            Assert.AreEqual(builder.ConstantInt(101), mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }));
            Assert.AreEqual(builder.ConstantInt(25), mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(5) }));

            // Now write to a symbolic location. This should cause all the stores to flushed
            // and then dropped
            var symIndex = GetVariable("symIndex", BPLType.Int);
            mp.WriteMapAt(new List<Expr>() {builder.Identifier(symIndex)}, builder.ConstantInt(11));

            // Read back
            var m0AfterFlush = mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) });
            Assert.IsNull(ExprUtil.AsLiteral(m0AfterFlush));
            Assert.AreEqual("map[0 := 99][2 := 101][5 := 25][symIndex := 11][0]", m0AfterFlush.ToString());

            var m2AfterFlush = mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) });
            Assert.IsNull(ExprUtil.AsLiteral(m2AfterFlush));
            Assert.AreEqual("map[0 := 99][2 := 101][5 := 25][symIndex := 11][2]", m2AfterFlush.ToString());

            var m5AfterFlush = mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(5) });
            Assert.IsNull(ExprUtil.AsLiteral(m5AfterFlush));
            Assert.AreEqual("map[0 := 99][2 := 101][5 := 25][symIndex := 11][5]", m5AfterFlush.ToString());
        }

        [Test()]
        public void ReadAtIndexMis()
        {
            // Build var m:[int][int,bool]bool
            var innerMapTy = GetMapVariable(BPLType.Bool, BPLType.Int, BPLType.Bool);
            var outerMapTy = GetMapVariable(innerMapTy, BPLType.Int);


            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", outerMapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            // There are no stores so we should get a map select
            var indices = new List<Expr>() {
                builder.ConstantInt(0),
                builder.ConstantInt(1), builder.False
            };
            var read = mp.ReadMapAt(indices);
            var asMapSelect = ExprUtil.AsMapSelect(read);
            Assert.IsNotNull(asMapSelect);
            Assert.AreEqual("map[0][1, false]", asMapSelect.ToString());

            // Do concrete store
            mp.WriteMapAt(indices, builder.True);

            // Try reading back (should get constant back)
            var readBack = mp.ReadMapAt(indices);
            Assert.AreEqual(builder.True, readBack);

            // Force flushing by doing a read
            read = mp.Read();
            Assert.AreEqual("map[0 := map[0][1, false := true]]", read.ToString());

            // Should still be ble to read back directly
            readBack = mp.ReadMapAt(indices);
            Assert.AreEqual(builder.True, readBack);
        }

        [Test()]
        public void DirectWriteDropsConstantStores()
        {
            // Build var m:[int]bool;
            var mapTy = GetMapVariable(BPLType.Bool, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", mapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            // m[0] := false
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(0) }, builder.False);

            // m[2] := true
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(2) }, builder.True);

            // The above stores aren't flushed. Do a direct write and then read
            // the stores should not be flushed.
            mp.Write(mapId);
            Assert.AreEqual("map", mp.Read().ToString());
        }

        [Test()]
        public void DirectWriteDropsNonAliasingSymbolicStores()
        {
            // Build var m:[int]bool;
            var mapTy = GetMapVariable(BPLType.Bool, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", mapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            var sym = builder.Identifier(GetVariable("sym", BPLType.Int));

            // m[1 + sym] := true
            mp.WriteMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym) }, builder.True);

            // Read back directly
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym)}));

            var sym2 = builder.Identifier(GetVariable("sym2", BPLType.Int));

            // m[sym2] := true
            mp.WriteMapAt(new List<Expr>() { sym2 }, builder.True);

            // The above stores aren't flushed. Do a direct write and then read
            // the stores should not be flushed.
            mp.Write(mapId);
            Assert.AreEqual("map", mp.Read().ToString());
        }

        [Test()]
        public void WriteMakesStoresInaccessible()
        {
            // Build var m:[int]bool;
            var mapTy = GetMapVariable(BPLType.Bool, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", mapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            // m[0] := false
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(0) }, builder.False);

            // m[2] := true
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(2) }, builder.True);

            // Read back
            Assert.AreEqual(builder.False, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }));

            // Write at symbolic location should make reading the stores directly fail
            // and instead return the flushed expression
            var symIndex = builder.Identifier(GetVariable("symIndex", BPLType.Int));
            mp.WriteMapAt(new List<Expr>() { symIndex }, builder.False);
            Assert.AreEqual("map[0 := false][2 := true][symIndex := false][0]", mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }).ToString());
            Assert.AreEqual("map[0 := false][2 := true][symIndex := false][2]", mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }).ToString());
        }

        [Test()]
        public void WritesAndMisRead()
        {
            // Build var m:[int]bool;
            var mapTy = GetMapVariable(BPLType.Bool, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", mapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            // m[0] := false
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(0) }, builder.False);

            // m[2] := true
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(2) }, builder.True);

            // Read back
            Assert.AreEqual(builder.False, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }));

            // Read from location not stored. Should cause stores to be flushed
            var readAtNonStoredLocation = mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(1) });
            Assert.IsNotNull(ExprUtil.AsMapSelect(readAtNonStoredLocation));
            Assert.AreEqual("map[0 := false][2 := true][1]", readAtNonStoredLocation.ToString());

            // Check read again
            Assert.AreEqual("map[0 := false][2 := true]", mp.Read().ToString());

            // Try reading from another location 
            var readAtStoredLocation = mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) });
            Assert.AreEqual(builder.True, readAtStoredLocation);


            // This definitely isn't known about
            var read3AtNonStoredLocation = mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(18) });
            Assert.IsNotNull(ExprUtil.AsMapSelect(read3AtNonStoredLocation));
            Assert.AreEqual("map[0 := false][2 := true][18]", read3AtNonStoredLocation.ToString());

            // Do another write and check we can read it back direcly
            // m[18] := false
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(18) }, builder.False);
            // Read back
            Assert.AreEqual(builder.False, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(18) }));
        }

        [Test()]
        public void MultipleWritesAndClone()
        {
            // Build var m:[int]bool;
            var mapTy = GetMapVariable(BPLType.Bool, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", mapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            // m[0] := false
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(0) }, builder.False);

            // m[2] := true
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(2) }, builder.True);

            // Read back
            Assert.AreEqual(builder.False, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }));

            // Clone and make sure we can read the same
            var clonedMp = mp.Clone(1);

            Assert.AreEqual(builder.False, clonedMp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));
            Assert.AreEqual(builder.True, clonedMp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }));

            // Modify the original and check the clone is unchanged
            var symBool = builder.Identifier(GetVariable("symBool", BPLType.Bool));
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(0) }, symBool);
            Assert.AreEqual(symBool, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));
            Assert.AreEqual(builder.False, clonedMp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));
            Assert.AreEqual("map[0 := symBool][2 := true]", mp.Read().ToString());
            Assert.AreEqual("map[0 := false][2 := true]", clonedMp.Read().ToString());

            // Modify the clone and check the original is unchanged
            clonedMp.WriteMapAt(new List<Expr>() { builder.ConstantInt(2) }, symBool);
            Assert.AreEqual(symBool, clonedMp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }));
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }));


            Assert.AreEqual("map[0 := false][2 := symBool]", clonedMp.Read().ToString());

            Assert.AreEqual("map[0 := symBool][2 := true]", mp.Read().ToString());
        }

        [Test()]
        public void AliasingSymbolicWrites()
        {
            // Build var m:[int]bool;
            var mapTy = GetMapVariable(BPLType.Bool, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", mapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            var sym = builder.Identifier(GetVariable("sym", BPLType.Int));
            var sym2 = builder.Identifier(GetVariable("sym2", BPLType.Int));

            // m[sym + sym2] := true
            mp.WriteMapAt(new List<Expr>() { builder.Add(sym2, sym) }, builder.True);

            // Read back
            Assert.AreEqual("true", mp.ReadMapAt(new List<Expr>() { builder.Add(sym2, sym) }).ToString());

            // Read back should give fully flushed expression
            Assert.AreEqual("map[sym2 + sym := true][sym2 + sym2]", mp.ReadMapAt(new List<Expr>() { builder.Add(sym2, sym2) }).ToString());
        }

        [Test()]
        public void MultipleNonAliasingSymbolicWritesAndClone()
        {
            // Build var m:[int]bool;
            var mapTy = GetMapVariable(BPLType.Bool, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", mapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            var sym = builder.Identifier(GetVariable("sym", BPLType.Int));

            // m[1 + sym] := true
            mp.WriteMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym) }, builder.True);

            // m[sym] := false
            mp.WriteMapAt(new List<Expr>() { sym }, builder.False);

            // Read back
            Assert.AreEqual(builder.False, mp.ReadMapAt(new List<Expr>() { sym }));
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym) }));


            // Clone and make sure we can read the same
            var clonedMp = mp.Clone(1);

            Assert.AreEqual(builder.False, clonedMp.ReadMapAt(new List<Expr>() { sym }));
            Assert.AreEqual(builder.True, clonedMp.ReadMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym) }));

            // Modify the original and check the clone is unchanged
            var symBool = builder.Identifier(GetVariable("symBool", BPLType.Bool));
            mp.WriteMapAt(new List<Expr>() { sym }, symBool);
            Assert.AreEqual(symBool, mp.ReadMapAt(new List<Expr>() { sym  }));
            Assert.AreEqual(builder.False, clonedMp.ReadMapAt(new List<Expr>() { sym }));

            // FIXME: Non-determinstically fails due to non determinisic ordering of stores
            //Assert.AreEqual("map[1 + sym := true][sym := symBool]", mp.Read().ToString());
            //Assert.AreEqual("map[1 + sym := true][sym := false]", clonedMp.Read().ToString());

            // Modify the clone and check the original is unchanged
            clonedMp.WriteMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym) }, symBool);
            Assert.AreEqual(symBool, clonedMp.ReadMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym) }));
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym) }));

            // FIXME: Check the ouput of Read(). Can't really do it due to non-deterministic ordering
        }

        [Test()]
        public void FlushMultipleWrites()
        {
            // Build var m:[int]bool;
            var mapTy = GetMapVariable(BPLType.Bool, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", mapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            // m[0] := false
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(0) }, builder.False);

            // m[2] := true
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(2) }, builder.True);

            // m[5] := false
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(5) }, builder.False);

            // Overwrite
            // m[5] := true
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(5) }, builder.True);

            // Read back
            Assert.AreEqual(builder.False, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }));
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(5) }));

            // Force flush
            var fullResult = mp.Read();
            var asMapStore = ExprUtil.AsMapStore(fullResult);
            Assert.IsNotNull(asMapStore);
            Assert.AreEqual("map[0 := false][2 := true][5 := true]", asMapStore.ToString());

            // Do again check we get the same
            fullResult = mp.Read();
            asMapStore = ExprUtil.AsMapStore(fullResult);
            Assert.IsNotNull(asMapStore);
            Assert.AreEqual("map[0 := false][2 := true][5 := true]", asMapStore.ToString());

            // The read should not clear the stores so we will read back the stored expression
            Assert.AreEqual(builder.False, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }));
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(5) }));

            // Reading at a index not stored should give full expression
            Assert.AreEqual("map[0 := false][2 := true][5 := true][1]", mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(1) }).ToString());
            Assert.AreEqual("map[0 := false][2 := true][5 := true][3]", mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(3) }).ToString());
            Assert.AreEqual("map[0 := false][2 := true][5 := true][4]", mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(4) }).ToString());
        }

        [Test()]
        public void WriteAtConstantIndicesDoIndexedReadThenFlush()
        {
            // Build var m:[int][int][int]bool
            var innerMapTy = GetMapVariable(BPLType.Bool, BPLType.Int);
            var middleMapTy = GetMapVariable(innerMapTy, BPLType.Int);
            var outerMapTy = GetMapVariable(middleMapTy, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", outerMapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            // do m[1][2][3] := False
            var indices = new List<Expr>() { builder.ConstantInt(1), builder.ConstantInt(2), builder.ConstantInt(3)  };
            mp.WriteMapAt(indices, builder.False);

            // Read back by index
            var indexedRead = mp.ReadMapAt(indices);
            Assert.AreEqual(builder.False, indexedRead);

            // Force the expressions to be flushed
            var fullRead = mp.Read();
            var asMapStore = ExprUtil.AsMapStore(fullRead);
            Assert.IsNotNull(asMapStore);
            Assert.AreEqual("map[1 := map[1][2 := map[1][2][3 := false]]]", asMapStore.ToString());

            // We only did a read so should still be able to get the stored expression
            Assert.AreEqual(builder.False, mp.ReadMapAt(indices));
        }

        [Test()]
        public void WriteSymbolicIndexNestedMapAndReadBack()
        {
            // Build var m:[int][int,bool]bool
            var innerMapTy = GetMapVariable(BPLType.Bool, BPLType.Int, BPLType.Bool);
            var outerMapTy = GetMapVariable(innerMapTy, BPLType.Int);


            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", outerMapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            // Build indicies, deliberately make sure that it would be difficult
            // to tell if they could alias.

            var x = builder.Identifier(GetVariable("x", BPLType.Bool));
            var y = builder.Identifier(GetVariable("y", BPLType.Bool));
            var boolIndex = builder.And(x, y);

            var a = builder.Identifier(GetVariable("a", BPLType.Int));
            var b = builder.Identifier(GetVariable("b", BPLType.Int));
            var firstIntIndex = builder.Add(a, b);

            var e = builder.Identifier(GetVariable("e", BPLType.Int));
            var f = builder.Identifier(GetVariable("f", BPLType.Int));
            var secondIntIndex = builder.Add(e, f);


            var indices = new List<Expr>() { firstIntIndex, secondIntIndex, boolIndex };
            // m[ a + b := m[a+b][e+f, x+y := true]
            mp.WriteMapAt(indices, builder.True);

            // Read back and check
            var result = mp.Read();
            Assert.AreEqual("map[a + b := map[a + b][e + f, x && y := true]]", result.ToString());

        }

        [Test()]
        public void WriteAtSymbolicNonAliasingIndices()
        {
            // Build var m:[int]bool;
            var mapTy = GetMapVariable(BPLType.Bool, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", mapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            var sym = builder.Identifier(GetVariable("sym", BPLType.Int));

            // m[sym] := false
            mp.WriteMapAt(new List<Expr>() { sym }, builder.False);

            // m[1 + sym] := true
            mp.WriteMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym) }, builder.True);

            // Read back directly
            Assert.AreEqual(builder.False, mp.ReadMapAt(new List<Expr>() { sym }));
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym)}));

            // Overwrite
            // m[1 + sym] := false
            mp.WriteMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym) }, builder.False);
            Assert.AreEqual(builder.False, mp.ReadMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym)}));

            // FIXME: We probably don't want non-determinism in symbooglix
            // Get full expression, we have to do it this way because there's no explicit ordering of the stores.
            // and the ordering appears to be random
            var fullExprAsString = mp.Read().ToString();
            if (fullExprAsString != "map[1 + sym := false][sym := false]" && fullExprAsString != "map[sym := false][1 + sym := false]")
                Assert.Fail("wrong result");
            //Assert.AreEqual("map[1 + sym := true][sym := false]", mp.Read().ToString());

            // Check we can still read back directly
            Assert.AreEqual(builder.False, mp.ReadMapAt(new List<Expr>() { sym }));
            Assert.AreEqual(builder.False, mp.ReadMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym)}));

            // Try reading from a location not stored.
            var mOffsetTwo = mp.ReadMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(2), sym) });
            Assert.AreEqual(fullExprAsString + "[2 + sym]", mOffsetTwo.ToString());
        }

        [Test()]
        public void WriteAtSymbolicNonAliasingIndicesThenConcrete()
        {
            // Build var m:[int]bool;
            var mapTy = GetMapVariable(BPLType.Bool, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", mapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            var sym = builder.Identifier(GetVariable("sym", BPLType.Int));

            // m[1 + sym] := true
            mp.WriteMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym) }, builder.True);

            // Read back directly
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym)}));

            // Now write to a concrete location
            // This should flush the stores at the symbolic locations

            // m[0] := false
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(0) }, builder.False);

            // Read back directly
            Assert.AreEqual(builder.False, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));

            // Read back at the symbolic location. It shouldn't be directly accessible anymore and
            // we should get the fully flushed expression
            Assert.AreEqual("map[1 + sym := true][0 := false][1 + sym]", mp.ReadMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym)}).ToString());

            // Read back full expression
            Assert.AreEqual("map[1 + sym := true][0 := false]", mp.Read().ToString());

            // Now write to a symbolic location
            // This should flush the stores at concrete locations

            // m[3 + sym] := false
            mp.WriteMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(3), sym) }, builder.True);

            // Should be a flushed expression rather than "false"
            Assert.AreEqual("map[1 + sym := true][0 := false][3 + sym := true][0]", mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }).ToString());
        }

        [Test()]
        public void WriteAtSymbolicNonAliasAndThenWriteAtNewAliasingLocations()
        {
            // Build var m:[int]bool;
            var mapTy = GetMapVariable(BPLType.Bool, BPLType.Int);

            // Build map variable variable
            var builder = GetSimpleExprBuilder();
            var mv = GetVariable("map", mapTy);
            var mapId = builder.Identifier(mv);
            var mp = GetMapProxy(mapId);

            var sym = builder.Identifier(GetVariable("sym", BPLType.Int));

            // m[1 + sym] := true
            mp.WriteMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym) }, builder.True);

            // Read back directly
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(1), sym)}));

            var sym2 = builder.Identifier(GetVariable("sym2", BPLType.Int));

            // m[sym2] := true
            mp.WriteMapAt(new List<Expr>() { sym2 }, builder.True);

            // Note the ConstantFoldingExprBuilder manages to extract the true for us
            Assert.AreEqual("true", mp.ReadMapAt( new List<Expr>() {sym2}).ToString());

            // Read from symoblic location where we don't know if it aliases with existing stores. This
            // will force full flush
            Assert.AreEqual("map[1 + sym := true][sym2 := true][sym]", mp.ReadMapAt( new List<Expr>() {sym}).ToString());

            // The next write to this non-aliasing location should be readable directly
            // m[3 + sym2] := true
            mp.WriteMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(3), sym2) }, builder.True);
            Assert.AreEqual(builder.True, mp.ReadMapAt( new List<Expr>() {builder.Add(builder.ConstantInt(3), sym2)}));

            mp.WriteMapAt(new List<Expr>() { builder.Add(builder.ConstantInt(2), sym2) }, builder.False);
            Assert.AreEqual(builder.False, mp.ReadMapAt( new List<Expr>() {builder.Add(builder.ConstantInt(2), sym2)}));
        }
    }
}

