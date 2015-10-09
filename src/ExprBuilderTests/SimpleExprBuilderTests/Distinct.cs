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
using System.Collections.Generic;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class Distinct : SimpleExprBuilderTestBase
    {
        [Test()]
        public void CreateSimpleVars()
        {
            var builder = GetSimpleBuilder();
            var v0 = GetVarAndIdExpr("v0", BasicType.Bool);
            var v1 = GetVarAndIdExpr("v1", BasicType.Bool);

            var distinctExpr = builder.Distinct(new List<Expr>() { v0.Item2, v1.Item2 });
            var distinctExpr2 = builder.Distinct(new List<Expr>() { v0.Item2, v1.Item2 });
            Assert.AreEqual(distinctExpr.GetHashCode(), distinctExpr2.GetHashCode());
            Assert.IsTrue(distinctExpr.Equals(distinctExpr2));
            Assert.AreEqual("distinct(v0, v1)", distinctExpr.ToString());
            CheckIsBoolType(distinctExpr);
            CheckIsBoolType(distinctExpr2);
        }

        [TestCase(1)]
        [TestCase(10)]
        [TestCase(100)]
        public void CreateNestedExpr(int depth)
        {
            var builder = GetSimpleBuilder();
            var v0 = GetVarAndIdExpr("v0", BasicType.Int);
            var v1 = GetVarAndIdExpr("v1", BasicType.Int);

            var args0 = new List<Expr>();
            var args1 = new List<Expr>();
            Expr e0 = v0.Item2;
            Expr e1 = v0.Item2;
            for (int count = 0; count < depth; ++count)
            {
                e0 = builder.Add(v1.Item2, e0);
                e1 = builder.Add(v1.Item2, e1);
                args0.Add(e0);
                args1.Add(e1);
            }

            var distinctExpr0 = builder.Distinct(args0);
            var distinctExpr1 = builder.Distinct(args1);
            Assert.AreEqual(distinctExpr0.GetHashCode(), distinctExpr1.GetHashCode());
            Assert.AreEqual(distinctExpr0, distinctExpr1);
            CheckIsBoolType(distinctExpr0);
            CheckIsBoolType(distinctExpr1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void MisMatchTypes()
        {
            var builder = GetSimpleBuilder();
            var v0 = GetVarAndIdExpr("v0", BasicType.Bool);
            var v1 = GetVarAndIdExpr("v1", BasicType.Int);
            builder.Distinct(new List<Expr>() { v0.Item2, v1.Item2 });
        }
    }
}

