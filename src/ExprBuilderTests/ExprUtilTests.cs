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
using Symbooglix;
using Microsoft.Boogie;
using System.Diagnostics;
using BType = Microsoft.Boogie.Type;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class ExprUtilTests : SimpleExprBuilderTestBase
    {
        [Test()]
        public void AsLiteralWithLiteral()
        {
            var sb = GetSimpleBuilder();
            var lit = sb.True;
            Assert.IsInstanceOf<LiteralExpr>(lit);
            var asLit = ExprUtil.AsLiteral(lit);
            Assert.IsNotNull(asLit);
            Assert.AreSame(lit, asLit);
        }

        [Test()]
        public void AsLiteralWithNonLiteral()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var e = sb.Eq(v, sb.False);
            Assert.IsNotInstanceOf<LiteralExpr>(e);
            var asLit = ExprUtil.AsLiteral(e);
            Assert.IsNull(asLit);
        }

        [Test()]
        public void IsTrueWithTrue()
        {
            var sb = GetSimpleBuilder();
            var e = sb.True;
            Assert.IsTrue(ExprUtil.IsTrue(e));
        }

        [Test()]
        public void IsTrueWithFalse()
        {
            var sb = GetSimpleBuilder();
            var e = sb.False;
            Assert.IsFalse(ExprUtil.IsTrue(e));
        }

        [Test()]
        public void IsTrueWithWithExpr()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var e = sb.Eq(v, sb.False);
            Assert.IsFalse(ExprUtil.IsTrue(e));
        }

        [Test()]
        public void IsFalseWithTrue()
        {
            var sb = GetSimpleBuilder();
            var e = sb.True;
            Assert.IsFalse(ExprUtil.IsFalse(e));
        }

        [Test()]
        public void IsFalseWithFalse()
        {
            var sb = GetSimpleBuilder();
            var e = sb.False;
            Assert.IsTrue(ExprUtil.IsFalse(e));
        }

        [Test()]
        public void IsFalseWithWithExpr()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var e = sb.Eq(v, sb.False);
            Assert.IsFalse(ExprUtil.IsFalse(e));
        }

        [Test()]
        public void IsIfThenElseWithIte()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var ite = sb.IfThenElse(sb.Eq(v, sb.False), v, sb.False);
            var asIte = ExprUtil.AsIfThenElse(ite);
            Assert.IsNotNull(asIte);
            Assert.AreSame(ite, asIte);
        }

        [Test()]
        public void IsIfThenElseWithAnd()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var ite = sb.And(sb.Eq(v, sb.False), v);
            var asIte = ExprUtil.AsIfThenElse(ite);
            Assert.IsNull(asIte);
        }

        [Test()]
        public void IsNotWithNot()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var e = sb.Not(v);
            var asNot = ExprUtil.AsNot(e);
            Assert.IsNotNull(asNot);
            Assert.AreSame(e, asNot);
        }

        [Test()]
        public void IsNotWithAnd()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var e = sb.And(v, v);
            var asNot = ExprUtil.AsNot(e);
            Assert.IsNull(asNot);
        }

        [Test()]
        public void AsBVSEXTWithBVSEXT()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.GetBvType(4)).Item2;
            var sext = sb.BVSEXT(v, 8);
            var asBvSExt = ExprUtil.AsBVSEXT(sext);
            Assert.IsNotNull(asBvSExt);
        }

        [Test()]
        public void AsBVSEXTWithoutBVSEXT()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.GetBvType(4)).Item2;
            var sext = sb.BVADD(v, v);
            var asBvSExt = ExprUtil.AsBVSEXT(sext);
            Assert.IsNull(asBvSExt);
        }

        [Test()]
        public void AsNotEqWithNotEq()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.GetBvType(4)).Item2;
            var e = sb.NotEq(v, sb.ConstantBV(0, 4));
            var asNotEq = ExprUtil.AsNotEq(e);
            Assert.IsNotNull(asNotEq);
            Assert.AreSame(e, asNotEq);
        }

        [Test()]
        public void AsNotEqWithoutNotEq()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.GetBvType(4)).Item2;
            var e = sb.Eq(v, sb.ConstantBV(0, 4));
            var asNotEq = ExprUtil.AsNotEq(e);
            Assert.IsNull(asNotEq);
        }

        [Test()]
        public void AsLtWithLt()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Int).Item2;
            var e = sb.Lt(v, sb.ConstantInt(0));
            var asLt = ExprUtil.AsLt(e);
            Assert.IsNotNull(asLt);
            Assert.AreSame(e, asLt);
        }

        [Test()]
        public void AsLtWithoutLt()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Int).Item2;
            var e = sb.Eq(v, sb.ConstantInt(0));
            var asLt = ExprUtil.AsLt(e);
            Assert.IsNull(asLt);
        }

        [Test()]
        public void AsLeWithLe()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Int).Item2;
            var e = sb.Le(v, sb.ConstantInt(0));
            var asLe = ExprUtil.AsLe(e);
            Assert.IsNotNull(asLe);
            Assert.AreSame(e, asLe);
        }

        [Test()]
        public void AsLeWithoutLe()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Int).Item2;
            var e = sb.Eq(v, sb.ConstantInt(0));
            var asLe = ExprUtil.AsLe(e);
            Assert.IsNull(asLe);
        }

        [Test()]
        public void AsGtWithGt()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Int).Item2;
            var e = sb.Gt(v, sb.ConstantInt(0));
            var asGt = ExprUtil.AsGt(e);
            Assert.IsNotNull(asGt);
            Assert.AreSame(e, asGt);
        }

        [Test()]
        public void AsGtWithoutGt()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Int).Item2;
            var e = sb.Eq(v, sb.ConstantInt(0));
            var asGt = ExprUtil.AsGt(e);
            Assert.IsNull(asGt);
        }

        [Test()]
        public void AsGeWithGe()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Int).Item2;
            var e = sb.Ge(v, sb.ConstantInt(0));
            var asGe = ExprUtil.AsGe(e);
            Assert.IsNotNull(asGe);
            Assert.AreSame(e, asGe);
        }

        [Test()]
        public void AsGeWithoutGe()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Int).Item2;
            var e = sb.Eq(v, sb.ConstantInt(0));
            var asGe = ExprUtil.AsGe(e);
            Assert.IsNull(asGe);
        }

        [Test()]
        public void AsEqWithEq()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.GetBvType(4)).Item2;
            var e = sb.Eq(v, sb.ConstantBV(0, 4));
            var asEq = ExprUtil.AsEq(e);
            Assert.IsNotNull(asEq);
            Assert.AreSame(e, asEq);
        }

        [Test()]
        public void AsEqWithoutEq()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.GetBvType(4)).Item2;
            var e = sb.NotEq(v, sb.ConstantBV(0, 4));
            var asEq = ExprUtil.AsEq(e);
            Assert.IsNull(asEq);
        }

        [Test()]
        public void AsBVZEXTWithBVZEXT()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.GetBvType(4)).Item2;
            var zext = sb.BVZEXT(v, 8);
            var asBvZExt = ExprUtil.AsBVZEXT(zext);
            Assert.IsNotNull(asBvZExt);
        }

        [Test()]
        public void AsBVZEXTNotWithoutBVZEXT()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.GetBvType(4)).Item2;
            var zext = sb.BVADD(v, v);
            var asBvZExt = ExprUtil.AsBVZEXT(zext);
            Assert.IsNull(asBvZExt);
        }

        [TestCase(0, 4, false)]
        [TestCase(1, 4, false)]
        [TestCase(14, 4, false)]
        [TestCase(15, 4, true)]
        public void IsBVAllOnesTest(int valueDecRepr, int bitWidth, bool expectedTrue)
        {
            var sb = GetSimpleBuilder();
            var constant = sb.ConstantBV(valueDecRepr, bitWidth);
            CheckBVAllOnes(constant, expectedTrue);
        }

        private void CheckBVAllOnes(Expr e, bool expectedTrue)
        {
            if (expectedTrue)
                Assert.IsTrue(ExprUtil.IsBVAllOnes(e));
            else
                Assert.IsFalse(ExprUtil.IsBVAllOnes(e));
        }

        public void IsBVAllOnesWrongTypes()
        {
            var sb = GetSimpleBuilder();
            CheckBVAllOnes(sb.True, false);
            CheckBVAllOnes(sb.False, false);
            CheckBVAllOnes(sb.ConstantInt(0), false);
            CheckBVAllOnes(sb.ConstantReal("1.0"), false);
        }

        [TestCase(1)]
        [TestCase(10)]
        //[TestCase(1000), Ignore("FIXME: hash code computation is slow on construction")]
        public void StructurallyEqualWithRef(int depth)
        {
            var sb = GetSimpleBuilder();
            Expr e = sb.True;
            for (int i = 0; i < depth; ++i)
            {
                e = sb.Or(e, sb.And(e, e));
            }
            Assert.IsTrue(ExprUtil.StructurallyEqual(e, e));
        }

        [TestCase(1)]
        [TestCase(10)]
        [TestCase(13)] // Using a value much larger than this causes the test to take too long because a full Equals() must be performed.
        public void StructurallyEqualWithDifferentRef(int depth)
        {
            var sb = GetSimpleBuilder();
            Expr e0 = sb.True;
            for (int i = 0; i < depth; ++i)
            {
                e0 = sb.Or(e0, sb.And(e0, e0));
            }

            Expr e1 = sb.True;
            for (int i = 0; i < depth; ++i)
            {
                e1 = sb.Or(e1, sb.And(e1, e1));
            }
            Assert.AreEqual(e0.GetHashCode(), e1.GetHashCode());
            Assert.IsTrue(ExprUtil.StructurallyEqual(e0, e1));
        }

        [TestCase(1)]
        [TestCase(10)]
        [TestCase(100)]
        public void StructurallyNotEqualWithDifferentRef(int depth)
        {
            var sb = GetSimpleBuilder();
            Expr e0 = sb.True;
            for (int i = 0; i < depth; ++i)
            {
                e0 = sb.Or(e0, sb.And(e0, e0));
            }

            Expr e1 = sb.True;
            for (int i = 0; i < depth +1; ++i)
            {
                e1 = sb.Or(e1, sb.And(e1, e1));
            }
            Assert.AreNotEqual(e0.GetHashCode(), e1.GetHashCode());
            Assert.IsFalse(ExprUtil.StructurallyEqual(e0, e1));
        }

        [Test()]
        public void NotUninterpretedFunction() {
            var sb = GetSimpleBuilder();
            var constant = sb.ConstantBV(0, 32); // 0bv32
            var addConstants = sb.BVADD(constant, constant);
            var asUF = ExprUtil.AsUninterpretedFunctionCall(addConstants);
            Assert.IsNull(asUF);

            // Yuck...
            var func = ((addConstants as NAryExpr).Fun as FunctionCall).Func;
            Assert.IsNull(ExprUtil.AsUninterpretedFunction(func));
        }

        [Test()]
        public void UninterpretedFunction() {
            var FCB = new Symbooglix.FunctionCallBuilder();
            var funcCall = FCB.CreateCachedUninterpretedFunctionCall(
                "foo",
                BType.Bool, // Return type
                new List<Microsoft.Boogie.Type>() {
                    BType.GetBvType(32), BType.GetBvType(32)
                }
            );

            Assert.IsNotNull(ExprUtil.AsUninterpretedFunction(funcCall.Func));

            var sb = GetSimpleBuilder();
            var callFunc = sb.UFC(funcCall, sb.ConstantBV(0, 32), sb.ConstantBV(1, 32));
            var asUF = ExprUtil.AsUninterpretedFunctionCall(callFunc);
            Assert.IsNotNull(asUF);
        }
    }
}

