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
using System.Linq;

using BPLType = Microsoft.Boogie.Type;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class MapStoreSelectSimpleBuilder : SimpleExprBuilderTestBase
    {
        // Map select
        [TestCase()]
        public void SimpleMapSelect()
        {
            // var x:[int]bool;
            var id = GetMapVariable("x", BasicType.Bool, BasicType.Int).Item1;
            var builder = GetSimpleBuilder();

            // x[0]
            var result = builder.MapSelect(id, builder.ConstantInt(0));
            Assert.AreEqual("x[0]", result.ToString());
            CheckType(result, p => p.IsBool);
        }

        [TestCase(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SimpleMapSelectWrongIndexType()
        {
            // var x:[bv8]bool;
            var id = GetMapVariable("x", BasicType.Bool, BasicType.GetBvType(8)).Item1;
            var builder = GetSimpleBuilder();

            // x[0]
            builder.MapSelect(id, builder.ConstantInt(0));
        }

        [TestCase(), ExpectedException(typeof(ArgumentException))]
        public void SimpleMapSelectWrongArity()
        {
            // var x:[bv8]bool;
            var id = GetMapVariable("x", BasicType.Bool, BasicType.Int, BasicType.Int).Item1;
            var builder = GetSimpleBuilder();

            // x[0]
            builder.MapSelect(id, builder.ConstantInt(0));
        }

        [TestCase()]
        public void TwoIndicesMapSelect()
        {
            // var x:[int, int]bool;
            var id = GetMapVariable("x", BasicType.Bool, BasicType.Int, BasicType.Int).Item1;
            var builder = GetSimpleBuilder();

            // x[0, 1]
            var result = builder.MapSelect(id, builder.ConstantInt(0), builder.ConstantInt(1));
            Assert.AreEqual("x[0, 1]", result.ToString());
            CheckType(result, p => p.IsBool);
        }

        // FIXME: Boogie's typechecker actually seems to allow this. This seems crazy why would
        // you want a map without any arguments? You might as well just have a regular variable.
        [TestCase(),ExpectedException(typeof(ArgumentException))]
        public void NoIndicesMapSelect()
        {
            // var x:[]bool;
            var id = GetMapVariable("x", BasicType.Bool).Item1;
            var builder = GetSimpleBuilder();

            // x[]
            var result = builder.MapSelect(id);
            Assert.AreEqual("x[]", result.ToString());
            CheckType(result, p => p.IsBool);
        }

        [TestCase()]
        public void NestedMapSelect()
        {
            // var [int, int]bool; (we don't need the variable)
            var mapType = GetMapVariable("x", BasicType.Bool, BasicType.Int, BasicType.Int).Item2;

            // var y:[bool][int, int]bool;
            var vtPair = GetMapVariable("y", mapType, BasicType.Bool);
            var id = vtPair.Item1;

            var builder = GetSimpleBuilder();

            // y[true]
            var firstSelect = builder.MapSelect(id, builder.True);
            Assert.AreEqual("y[true]", firstSelect.ToString());
            CheckType(firstSelect, p => p.IsMap);
            Assert.AreEqual(mapType, firstSelect.Type);

            // y[true][0,1]
            var secondSelect = builder.MapSelect(firstSelect, builder.ConstantInt(0), builder.ConstantInt(1));
            Assert.AreEqual("y[true][0, 1]", secondSelect.ToString());
            CheckType(secondSelect, p => p.IsBool);
        }

        // Map store
        [TestCase()]
        public void SimpleMapStore()
        {
            // var x:[int]bool;
            var vtPair = GetMapVariable("x", BasicType.Bool, BasicType.Int);
            var id = vtPair.Item1;
            var mapType = vtPair.Item2;
            var builder = GetSimpleBuilder();

            // x[0 := true]
            var result = builder.MapStore(id, builder.True, builder.ConstantInt(0));
            Assert.AreEqual("x[0 := true]", result.ToString());
            CheckType(result, p => p.Equals(mapType));

            // Add another store to the existing store
            // x[0 := true][ 0:= false]
            var result2 = builder.MapStore(result, builder.False, builder.ConstantInt(0));
            Assert.AreEqual("x[0 := true][0 := false]", result2.ToString());
            CheckType(result2, p => p.Equals(mapType));
        }

        [TestCase(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SimpleMapStoreWrongIndexType()
        {
            // var x:[bv8]bool;
            var id = GetMapVariable("x", BasicType.Bool, BasicType.GetBvType(8)).Item1;
            var builder = GetSimpleBuilder();

            // x[0 := true] // wrong index type
            builder.MapStore(id, builder.True, builder.ConstantInt(0));
        }

        [TestCase(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SimpleMapStoreWrongValueType()
        {
            // var x:[bv8]bool;
            var id = GetMapVariable("x", BasicType.Bool, BasicType.GetBvType(8)).Item1;
            var builder = GetSimpleBuilder();

            // x[0bv8 := 0] // wrong value type assigned
            builder.MapStore(id, builder.ConstantInt(0), builder.ConstantBV(0,8));
        }

        [TestCase(), ExpectedException(typeof(ArgumentException))]
        public void SimpleMapStoreWrongArity()
        {
            // var x:[bv8]bool;
            var id = GetMapVariable("x", BasicType.Bool, BasicType.GetBvType(8)).Item1;
            var builder = GetSimpleBuilder();

            // x[0bv8,1bv8 := 0] // wrong number of indices
            builder.MapStore(id, builder.ConstantInt(0), builder.ConstantBV(0,8), builder.ConstantBV(1,8));
        }

        [TestCase()]
        public void TwoIndicesMapStore()
        {
            // var x:[int, int]bool;
            var vtPair = GetMapVariable("x", BasicType.Bool, BasicType.Int, BasicType.Int);
            var id = vtPair.Item1;
            var mapType = vtPair.Item2;
            var builder = GetSimpleBuilder();

            // x[0, 1]
            var result = builder.MapStore(id, builder.True, builder.ConstantInt(0), builder.ConstantInt(1));
            Assert.AreEqual("x[0, 1 := true]", result.ToString());
            CheckType(result, p => p.Equals(mapType));
        }

        // FIXME: Boogie's typechecker actually seems to allow this. This seems crazy why would
        // you want a map without any arguments? You might as well just have a regular variable.
        [TestCase(),ExpectedException(typeof(ArgumentException))]
        public void NoIndicesMapStore()
        {
            // var x:[]bool;
            var id = GetMapVariable("x", BasicType.Bool).Item1;
            var builder = GetSimpleBuilder();

            // x[ := true]
            var result = builder.MapStore(id, builder.True);
            Assert.AreEqual("x[ := true]", result.ToString());
            CheckType(result, p => p.IsBool);
        }
    }
}

