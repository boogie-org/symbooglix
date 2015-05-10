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
            return new MapProxy(initialValue);
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
        public void SymbolicReadAtIndex()
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

            // FIXME: The stored constants aren't directly accessible anymore, this a little annoying as we only did a read
            // but this is the current design
            readBack = mp.ReadMapAt(indices);
            Assert.AreEqual("map[0 := map[0][1, false := true]][0][1, false]", readBack.ToString());
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

            // Read from location not stored. Should cause stores to be flushed
            var readAtNonStoredLocation = mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(1) });
            Assert.IsNotNull(ExprUtil.AsMapSelect(readAtNonStoredLocation));
            Assert.AreEqual("map[0 := false][2 := true][1]", readAtNonStoredLocation.ToString());

            // Check read again
            Assert.AreEqual("map[0 := false][2 := true]", mp.Read().ToString());

            // Try reading from another location 
            // FIXME: We've done no writes but don't read back the known store
            var read2AtNonStoredLocation = mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) });
            Assert.IsNotNull(ExprUtil.AsMapSelect(read2AtNonStoredLocation));
            Assert.AreEqual("map[0 := false][2 := true][2]", read2AtNonStoredLocation.ToString());

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
            var clonedMp = mp.Clone();

            Assert.AreEqual(builder.False, clonedMp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));
            Assert.AreEqual(builder.True, clonedMp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }));

            // Modify the original and check the clone is unchanged
            var symBool = builder.Identifier(GetVariable("symBool", BPLType.Bool));
            mp.WriteMapAt(new List<Expr>() { builder.ConstantInt(0) }, symBool);
            Assert.AreEqual(symBool, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));
            Assert.AreEqual(builder.False, clonedMp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }));

            // Modify the clone and check the original is unchanged
            clonedMp.WriteMapAt(new List<Expr>() { builder.ConstantInt(2) }, symBool);
            Assert.AreEqual(symBool, clonedMp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }));
            Assert.AreEqual(builder.True, mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }));
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

            // The read will clear the stores so we will read back a full expression
            Assert.AreEqual("map[0 := false][2 := true][5 := true][0]", mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(0) }).ToString());
            Assert.AreEqual("map[0 := false][2 := true][5 := true][2]", mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(2) }).ToString());
            Assert.AreEqual("map[0 := false][2 := true][5 := true][5]", mp.ReadMapAt(new List<Expr>() { builder.ConstantInt(5) }).ToString());
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

            // FIXME: We only did a read but now we can't get the constants
            Assert.AreEqual("map[1 := map[1][2 := map[1][2][3 := false]]][1][2][3]", mp.ReadMapAt(indices).ToString());
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
    }
}

