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
    public class FoldMapSelect : ConstantFoldingExprBuilderTests
    {
        [TestCase(0)]
        [TestCase(1)]
        [TestCase(2)]
        public void SelectMapStoreDepthSingleIndex(int depth)
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.Bool).Item2;
            var map = GetMapVariable("m", BasicType.Bool, BasicType.Int).Item1;

            // The store that we want to get to
            var update = cfb.MapStore(map, id, cfb.ConstantInt(1));

            // Put multiple updates in front of the update we want to access
            for (int index = 0; index < depth; ++index)
                update = cfb.MapStore(update, cfb.False, cfb.ConstantInt(2 + index));

            // Now do a MapSelect from same location
            var result = cfb.MapSelect(update, cfb.ConstantInt(1));
            CheckIsBoolType(result);
            Assert.AreSame(id, result);
        }

        [TestCase(0)]
        [TestCase(1)]
        [TestCase(2)]
        public void SelectMapStoreDepthTwoIndices(int depth)
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.Bool).Item2;
            var map = GetMapVariable("m", BasicType.Bool, BasicType.Int, BasicType.Int).Item1;

            // The store that we want to get to
            var update = cfb.MapStore(map, id, cfb.ConstantInt(1), cfb.ConstantInt(-1));

            // Put multiple updates in front of the update we want to access
            for (int index = 0; index < depth; ++index)
                update = cfb.MapStore(update, cfb.False, cfb.ConstantInt(2 + index), cfb.ConstantInt(2 + index));

            // Now do a MapSelect from same location
            var result = cfb.MapSelect(update, cfb.ConstantInt(1), cfb.ConstantInt(-1));
            CheckIsBoolType(result);
            Assert.AreSame(id, result);
        }

        [TestCase(0)]
        [TestCase(1)]
        [TestCase(2)]
        public void SelectMapStoreSingleIndexRepeatedStoresToConcreteIndex(int depth)
        {
            var cfb = GetConstantFoldingBuilder();
            var map = GetMapVariable("m", BasicType.Int, BasicType.Int).Item1;

            var update = cfb.MapStore(map, cfb.ConstantInt(1), cfb.ConstantInt(1));

            // Add multiple updates to the same location
            for (int index = 0; index < depth; ++index)
                update = cfb.MapStore(update, cfb.ConstantInt(2 + index), cfb.ConstantInt(1));

            // Now do a MapSelect from same location
            var result = cfb.MapSelect(update, cfb.ConstantInt(1));
            CheckIsInt(result);

            // Now check we read the concrete value we expect
            var asLit = ExprUtil.AsLiteral(result);
            Assert.IsNotNull(asLit);
            Assert.AreEqual(BigNum.FromInt(1 + depth), asLit.asBigNum);
        }

        [TestCase(0)]
        [TestCase(1)]
        [TestCase(2)]
        public void SelectMapStoreStoresToSymbolicIndex(int depth)
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            var sb = builders.Item1;
            var cfb = builders.Item2;
            var map = GetMapVariable("m", BasicType.Int, BasicType.Int).Item1;
            var unconstrainedIndex = GetVarAndIdExpr("idx", BasicType.Int).Item2;

            var update = cfb.MapStore(map, cfb.ConstantInt(1), unconstrainedIndex);
            var updateSb = sb.MapStore(map, cfb.ConstantInt(1), unconstrainedIndex);

            // Add multiple updates to various locations, these should prevent accessing the deeply nested mapStore at unconstrainedIndex
            for (int index = 0; index < depth; ++index)
            {
                update = cfb.MapStore(update, cfb.ConstantInt(2 + index), cfb.ConstantInt(index));
                updateSb = sb.MapStore(updateSb, sb.ConstantInt(2 + index), cfb.ConstantInt(index));
            }

            // Now do a MapSelect from same location
            var result = cfb.MapSelect(update, unconstrainedIndex);
            var resultSb = sb.MapSelect(update, unconstrainedIndex);
            CheckIsInt(result);
            CheckIsInt(resultSb);

            if (depth == 0)
            {
                // Only in this case should we be able to get a concrete value back

                // Now check we read the concrete value we expect
                var asLit = ExprUtil.AsLiteral(result);
                Assert.IsNotNull(asLit);
                Assert.AreEqual(BigNum.FromInt(1), asLit.asBigNum);
            }
            else
            {
                Assert.IsNull(ExprUtil.AsLiteral(result));
                Assert.IsNotNull(ExprUtil.AsMapSelect(result));
                // The result should be structurally the same as what the non folding builder built (i.e no folding happened)
                Assert.AreEqual(resultSb, result);
            }
        }

        [Test()]
        public void noFoldInaccessibleVariable()
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            var sb = builders.Item1;
            var cfb = builders.Item2;
            var map = GetMapVariable("m", BasicType.Int, BasicType.Int).Item1;
            var unconstrainedIndex = GetVarAndIdExpr("idx", BasicType.Int).Item2;

            var update = cfb.MapStore(map, cfb.ConstantInt(1), unconstrainedIndex);
            var updateSb = sb.MapStore(map, sb.ConstantInt(1), unconstrainedIndex);

            // Add an update in front that should prevent any folding when trying
            // to do a MapSelect from unconstraintedIndex. Folding can't be legally
            // done here because the folder doesn't know if unconstrained Index
            // can be equal to the index we write to below
            update = cfb.MapStore(update, cfb.ConstantInt(2), cfb.ConstantInt(2));
            updateSb = sb.MapStore(updateSb, cfb.ConstantInt(2), cfb.ConstantInt(2));

            var result = cfb.MapSelect(update, unconstrainedIndex);
            var resultSb = sb.MapSelect(update, unconstrainedIndex);
            CheckIsInt(result);
            CheckIsInt(resultSb);
            Assert.AreEqual(resultSb, result);
        }

        [TestCase(0)]
        [TestCase(1)]
        [TestCase(2)]
        public void noFoldNoConcretesWithCorrectIndex(int depth)
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            var sb = builders.Item1;
            var cfb = builders.Item2;
            var map = GetMapVariable("m", BasicType.Int, BasicType.Int).Item1;

            var update = cfb.MapStore(map, cfb.ConstantInt(1), cfb.ConstantInt(1));
            var updateSb = sb.MapStore(map, cfb.ConstantInt(1), sb.ConstantInt(1));

            // Add multiple updates to various locations
            for (int index = 0; index < depth; ++index)
            {
                update = cfb.MapStore(update, cfb.ConstantInt(2 + index), cfb.ConstantInt(index));
                updateSb = sb.MapStore(updateSb, sb.ConstantInt(2 + index), cfb.ConstantInt(index));
            }

            // Now do a MapSelect from a location that was not written to
            var result = cfb.MapSelect(update, cfb.ConstantInt(-1));
            var resultSb = sb.MapSelect(update, sb.ConstantInt(-1));
            CheckIsInt(result);
            CheckIsInt(resultSb);
            Assert.AreEqual(resultSb, result);
        }

        [Test()]
        public void noFoldNoStores()
        {
            var builders = GetSimpleAndConstantFoldingBuilder();
            var sb = builders.Item1;
            var cfb = builders.Item2;
            var map = GetMapVariable("m", BasicType.Int, BasicType.Int).Item1;
            var result = cfb.MapSelect(map, cfb.ConstantInt(0));
            var resultSb = sb.MapSelect(map, sb.ConstantInt(0));
            CheckIsInt(result);
            CheckIsInt(resultSb);
            Assert.AreEqual(resultSb, result);
        }
    }
}

