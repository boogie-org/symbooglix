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

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldNeg : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void simpleInt()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Neg(cfb.ConstantInt(5));
            CheckIsInt(result);
            Assert.AreEqual("-5", result.ToString());
        }

        [Test()]
        public void simpleReal()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Neg(cfb.ConstantReal("5.0"));
            CheckIsReal(result);
            Assert.AreEqual("-5e0", result.ToString());
        }

        [TestCase(2)]
        [TestCase(3)]
        [TestCase(50)]
        public void nestedNegs(int depth)
        {
            var pair = GetVarAndIdExpr("foo", BasicType.Int);
            var variable = pair.Item1;
            var id = pair.Item2;
            var cfb = GetConstantFoldingBuilder();
            Expr result = id;
            for (int i = 0; i < depth; ++i)
            {
                result = cfb.Neg(result);
                CheckIsInt(result);
            }

            if (depth % 2 == 0)
            {
                Assert.AreSame(id, result);
            }
            else
            {
                var asNeg = ExprUtil.AsNeg(result);
                Assert.IsNotNull(asNeg);
                Assert.AreSame(id, asNeg.Args[0]);
            }
        }

        [Test()]
        public void noFold()
        {
            var pair = GetSimpleAndConstantFoldingBuilder();
            var sb = pair.Item1;
            var cfb = pair.Item2;
            var id = GetVarAndIdExpr("foo", BasicType.Int).Item2;
            var foldedResult = cfb.Neg(id);
            var simpleResult = sb.Neg(id);
            CheckIsInt(foldedResult);
            CheckIsInt(simpleResult);
            Assert.AreEqual(simpleResult, foldedResult);

            var asNeg = ExprUtil.AsNeg(foldedResult);
            Assert.IsNotNull(asNeg);
            Assert.AreSame(id, asNeg.Args[0]);
        }
    }
}

