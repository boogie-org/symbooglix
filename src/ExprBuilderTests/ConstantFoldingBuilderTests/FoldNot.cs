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
    public class FoldNot : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void simpleTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Not(cfb.True);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void simpleFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Not(cfb.False);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [Test()]
        public void notEq()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.Int).Item2;
            var rhsConst = cfb.ConstantInt(0);
            var e = cfb.Not(cfb.Eq(x, rhsConst));
            var asNotEq = ExprUtil.AsNotEq(e);
            Assert.IsNotNull(asNotEq);
            Assert.AreSame(rhsConst, asNotEq.Args[0]);
            Assert.AreSame(x, asNotEq.Args[1]);
        }

        [Test()]
        public void Gt()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.Int).Item2;
            var y = GetVarAndIdExpr("y", Microsoft.Boogie.Type.Int).Item2;
            var e = cfb.Not(cfb.Gt(x, y));
            var asLe = ExprUtil.AsLe(e);
            Assert.IsNotNull(asLe);
            Assert.AreSame(x, asLe.Args[0]);
            Assert.AreSame(y, asLe.Args[1]);
        }

        [Test()]
        public void Ge()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.Int).Item2;
            var y = GetVarAndIdExpr("y", Microsoft.Boogie.Type.Int).Item2;
            var e = cfb.Not(cfb.Ge(x, y));
            var asLt = ExprUtil.AsLt(e);
            Assert.IsNotNull(asLt);
            Assert.AreSame(x, asLt.Args[0]);
            Assert.AreSame(y, asLt.Args[1]);
        }

        [Test()]
        public void Lt()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.Int).Item2;
            var y = GetVarAndIdExpr("y", Microsoft.Boogie.Type.Int).Item2;
            var e = cfb.Not(cfb.Lt(x, y));
            var asGe = ExprUtil.AsGe(e);
            Assert.IsNotNull(asGe);
            Assert.AreSame(x, asGe.Args[0]);
            Assert.AreSame(y, asGe.Args[1]);
        }

        [Test()]
        public void Le()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.Int).Item2;
            var y = GetVarAndIdExpr("y", Microsoft.Boogie.Type.Int).Item2;
            var e = cfb.Not(cfb.Le(x, y));
            var asGt = ExprUtil.AsGt(e);
            Assert.IsNotNull(asGt);
            Assert.AreSame(x, asGt.Args[0]);
            Assert.AreSame(y, asGt.Args[1]);
        }

        [Test()]
        public void BVUGT()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var y = GetVarAndIdExpr("y", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var e = cfb.Not(cfb.BVUGT(x, y));
            var asBVULE = ExprUtil.AsBVULE(e);
            Assert.IsNotNull(asBVULE);
            Assert.AreSame(x, asBVULE.Args[0]);
            Assert.AreSame(y, asBVULE.Args[1]);
        }

        [Test()]
        public void BVUGE()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var y = GetVarAndIdExpr("y", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var e = cfb.Not(cfb.BVUGE(x, y));
            var asBVULT = ExprUtil.AsBVULT(e);
            Assert.IsNotNull(asBVULT);
            Assert.AreSame(x, asBVULT.Args[0]);
            Assert.AreSame(y, asBVULT.Args[1]);
        }

        [Test()]
        public void BVULT()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var y = GetVarAndIdExpr("y", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var e = cfb.Not(cfb.BVULT(x, y));
            var asBVUGE = ExprUtil.AsBVUGE(e);
            Assert.IsNotNull(asBVUGE);
            Assert.AreSame(x, asBVUGE.Args[0]);
            Assert.AreSame(y, asBVUGE.Args[1]);
        }

        [Test()]
        public void BVULE()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var y = GetVarAndIdExpr("y", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var e = cfb.Not(cfb.BVULE(x, y));
            var asBVUGT = ExprUtil.AsBVUGT(e);
            Assert.IsNotNull(asBVUGT);
            Assert.AreSame(x, asBVUGT.Args[0]);
            Assert.AreSame(y, asBVUGT.Args[1]);
        }

        [Test()]
        public void BVSGT()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var y = GetVarAndIdExpr("y", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var e = cfb.Not(cfb.BVSGT(x, y));
            var asBVSLE = ExprUtil.AsBVSLE(e);
            Assert.IsNotNull(asBVSLE);
            Assert.AreSame(x, asBVSLE.Args[0]);
            Assert.AreSame(y, asBVSLE.Args[1]);
        }

        [Test()]
        public void BVSGE()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var y = GetVarAndIdExpr("y", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var e = cfb.Not(cfb.BVSGE(x, y));
            var asBVSLT = ExprUtil.AsBVSLT(e);
            Assert.IsNotNull(asBVSLT);
            Assert.AreSame(x, asBVSLT.Args[0]);
            Assert.AreSame(y, asBVSLT.Args[1]);
        }

        [Test()]
        public void BVSLT()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var y = GetVarAndIdExpr("y", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var e = cfb.Not(cfb.BVSLT(x, y));
            var asBVSGE = ExprUtil.AsBVSGE(e);
            Assert.IsNotNull(asBVSGE);
            Assert.AreSame(x, asBVSGE.Args[0]);
            Assert.AreSame(y, asBVSGE.Args[1]);
        }

        [Test()]
        public void BVSLE()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var y = GetVarAndIdExpr("y", Microsoft.Boogie.Type.GetBvType(4)).Item2;
            var e = cfb.Not(cfb.BVSLE(x, y));
            var asBVSGT = ExprUtil.AsBVSGT(e);
            Assert.IsNotNull(asBVSGT);
            Assert.AreSame(x, asBVSGT.Args[0]);
            Assert.AreSame(y, asBVSGT.Args[1]);
        }


        [TestCase(2)]
        [TestCase(3)]
        [TestCase(50)]
        public void nestedNots(int depth)
        {
            var pair = GetVarAndIdExpr("foo", BasicType.Bool);
            var variable = pair.Item1;
            var id = pair.Item2;
            var cfb = GetConstantFoldingBuilder();
            Expr result = id;
            for (int i = 0; i < depth; ++i)
            {
                result = cfb.Not(result);
                CheckIsBoolType(result);
            }

            if (depth % 2 == 0)
            {
                Assert.AreSame(id, result);
            }
            else
            {
                var asNot = ExprUtil.AsNot(result);
                Assert.IsNotNull(asNot);
                Assert.AreSame(id, asNot.Args[0]);
            }
        }

        [Test()]
        public void noFold()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Not(id);
            CheckIsBoolType(result);
            var asNot = ExprUtil.AsNot(result);
            Assert.IsNotNull(asNot);
            Assert.AreSame(id, asNot.Args[0]);
        }
    }
}

