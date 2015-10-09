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
using System.Collections;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldMapStore : ConstantFoldingExprBuilderTests
    {
        [TestCase(1)]
        [TestCase(2)]
        [TestCase(50)]
        public void ConcreteStoreSameValue(int depth)
        {
            var cfb = GetConstantFoldingBuilder();
            var map = GetMapVariable("m", BasicType.Int, BasicType.Int, BasicType.Int).Item1;

            var id = GetVarAndIdExpr("value", BasicType.Int).Item2;
            Expr result = map;

            // Writes to the same concrete location should get folded
            for (int index = 0; index < depth; ++index)
            {
                var oldResult = result;
                result = cfb.MapStore(result, id, cfb.ConstantInt(0), cfb.ConstantInt(1));
                CheckIsMapType(result, BasicType.Int, BasicType.Int, BasicType.Int);

                if (index > 0)
                {
                    // The same location with the same value is repeatedly written to
                    // so we shouldn't create a new node for this case.
                    Assert.AreSame(oldResult, result);
                }
            }

            // Check we have a single map store
            var asMapStore = ExprUtil.AsMapStore(result);
            Assert.AreSame(map, asMapStore.Args[0]); // map written to
            Assert.AreEqual(cfb.ConstantInt(0), asMapStore.Args[1]); // first index
            Assert.AreEqual(cfb.ConstantInt(1), asMapStore.Args[2]); // second index
            Assert.AreSame(id, asMapStore.Args[3]); // value stored
        }

        [TestCase(1)]
        [TestCase(2)]
        [TestCase(50)]
        public void ConcreteStoreDifferentValues(int depth)
        {
            var cfb = GetConstantFoldingBuilder();
            var map = GetMapVariable("m", BasicType.Int, BasicType.Int, BasicType.Int).Item1;

            Expr id = null;
            Expr result = map;

            // Writes to the same concrete location should get folded, but here
            // the value being written each is different so we need to make a new node each time
            for (int index = 0; index < depth; ++index)
            {
                id = GetVarAndIdExpr("value" + index.ToString(), BasicType.Int).Item2;
                var oldResult = result;
                result = cfb.MapStore(result, id, cfb.ConstantInt(0), cfb.ConstantInt(1));
                Assert.AreNotSame(oldResult, result);
                CheckIsMapType(result, BasicType.Int, BasicType.Int, BasicType.Int);
            }

            // Check we have a single map store
            var asMapStore = ExprUtil.AsMapStore(result);
            Assert.AreSame(map, asMapStore.Args[0]); // map written to
            Assert.AreEqual(cfb.ConstantInt(0), asMapStore.Args[1]); // first index
            Assert.AreEqual(cfb.ConstantInt(1), asMapStore.Args[2]); // second index
            Assert.AreSame(id, asMapStore.Args[3]); // value stored
        }

        [TestCase(1)]
        [TestCase(2)]
        [TestCase(50)]
        public void SymbolicStoreSameValue(int depth)
        {
            var cfb = GetConstantFoldingBuilder();
            var map = GetMapVariable("m", BasicType.Int, BasicType.Int, BasicType.Int).Item1;
            var idx0 = GetVarAndIdExpr("idx0", BasicType.Int).Item2;
            var idx1 = GetVarAndIdExpr("idx0", BasicType.Int).Item2;
            var id = GetVarAndIdExpr("value", BasicType.Int).Item2;
            Expr result = map;

            // Writes to the same concrete location should get folded
            for (int index = 0; index < depth; ++index)
            {
                var oldResult = result;
                result = cfb.MapStore(result, id, idx0, idx1);
                CheckIsMapType(result, BasicType.Int, BasicType.Int, BasicType.Int);

                if (index > 0)
                {
                    // The same location with the same value is repeatedly written to
                    // so we shouldn't create a new node for this case.
                    Assert.AreSame(oldResult, result);
                }
            }

            // Check we have a single map store
            var asMapStore = ExprUtil.AsMapStore(result);
            Assert.AreSame(map, asMapStore.Args[0]); // map written to
            Assert.AreEqual(idx0, asMapStore.Args[1]); // first index
            Assert.AreEqual(idx1, asMapStore.Args[2]); // second index
            Assert.AreSame(id, asMapStore.Args[3]); // value stored
        }

        [TestCase(1)]
        [TestCase(2)]
        [TestCase(50)]
        public void SymbolicStoreDifferentValues(int depth)
        {
            var cfb = GetConstantFoldingBuilder();
            var map = GetMapVariable("m", BasicType.Int, BasicType.Int, BasicType.Int).Item1;
            var idx0 = GetVarAndIdExpr("idx0", BasicType.Int).Item2;
            var idx1 = GetVarAndIdExpr("idx0", BasicType.Int).Item2;

            Expr id = null;
            Expr result = map;

            // Writes to the same concrete location should get folded, but here
            // the value being written each is different so we need to make a new node each time
            for (int index = 0; index < depth; ++index)
            {
                id = GetVarAndIdExpr("value" + index.ToString(), BasicType.Int).Item2;
                var oldResult = result;
                result = cfb.MapStore(result, id, idx0, idx1);
                Assert.AreNotSame(oldResult, result);
                CheckIsMapType(result, BasicType.Int, BasicType.Int, BasicType.Int);
            }

            // Check we have a single map store
            var asMapStore = ExprUtil.AsMapStore(result);
            Assert.AreSame(map, asMapStore.Args[0]); // map written to
            Assert.AreEqual(idx0, asMapStore.Args[1]); // first index
            Assert.AreEqual(idx1, asMapStore.Args[2]); // second index
            Assert.AreSame(id, asMapStore.Args[3]); // value stored
        }


        [TestCase(1)]
        [TestCase(2)]
        [TestCase(50)]
        public void NoFoldConcreteStoreSameValueAtDifferentLocations(int depth)
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            var sb = builders.Item1;
            var cfb = builders.Item2;
            var map = GetMapVariable("m", BasicType.Int, BasicType.Int, BasicType.Int).Item1;

            var id = GetVarAndIdExpr("value", BasicType.Int).Item2;
            Expr result = map;
            Expr resultSb = map;

            // Writes to different concrete locations should not be folded
            for (int index = 0; index < depth; ++index)
            {
                var oldResult = result;
                result = cfb.MapStore(result, id, cfb.ConstantInt(index), cfb.ConstantInt(index));
                resultSb = sb.MapStore(resultSb, id, sb.ConstantInt(index), sb.ConstantInt(index));
                CheckIsMapType(result, BasicType.Int, BasicType.Int, BasicType.Int);
                CheckIsMapType(resultSb, BasicType.Int, BasicType.Int, BasicType.Int);
                Assert.AreNotSame(oldResult, result);

            }

            // Check we have a single map store
            Assert.IsNotNull(ExprUtil.AsMapStore(result));
            Assert.AreEqual(resultSb, result);
        }

        [TestCase(1)]
        [TestCase(2)]
        [TestCase(50)]
        public void NoFoldSymbolicStoreSameValueAtDifferentLocations(int depth)
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            var sb = builders.Item1;
            var cfb = builders.Item2;
            var map = GetMapVariable("m", BasicType.Int, BasicType.Int, BasicType.Int).Item1;

            var id = GetVarAndIdExpr("value", BasicType.Int).Item2;
            Expr result = map;
            Expr resultSb = map;

            // Writes to different concrete locations should not be folded
            for (int index = 0; index < depth; ++index)
            {
                var oldResult = result;
                var unconstrainedIndex = GetVarAndIdExpr("idx" +  index.ToString(), BasicType.Int).Item2;
                result = cfb.MapStore(result, id, unconstrainedIndex, unconstrainedIndex);
                resultSb = sb.MapStore(resultSb, id, unconstrainedIndex, unconstrainedIndex);
                CheckIsMapType(result, BasicType.Int, BasicType.Int, BasicType.Int);
                CheckIsMapType(resultSb, BasicType.Int, BasicType.Int, BasicType.Int);
                Assert.AreNotSame(oldResult, result);
            }

            // Check we have a single map store
            Assert.IsNotNull(ExprUtil.AsMapStore(result));
            Assert.AreEqual(resultSb, result);
        }
    }
}

