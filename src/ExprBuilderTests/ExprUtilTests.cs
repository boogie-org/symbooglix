using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;
using System.Diagnostics;

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

        [TestCase(0, 4, false, 0, 0)] // 0b0000
        [TestCase(1, 4, true, 0, 0)] // 0b0001 <contiguous>
        [TestCase(2, 4, true, 1, 1)] // 0b0010 <contiguous>
        [TestCase(3, 4, true, 0, 1)] // 0b0011 <contiguous>
        [TestCase(4, 4, true, 2, 2)] // 0b0100 <contiguous>
        [TestCase(5, 4, false, 0, 0)] // 0b0101
        [TestCase(6, 4, true, 1, 2)] // 0b0110 <contiguous>
        [TestCase(7, 4, true, 0, 2)] // 0b0111 <contiguous>
        [TestCase(8, 4, true, 3, 3)] // 0b1000 <contiguous>
        [TestCase(9, 4, false, 0, 0)] // 0b1001
        [TestCase(10, 4, false, 0, 0)] // 0b1010
        [TestCase(11, 4, false, 0, 0)] // 0b1011
        [TestCase(12, 4, true, 2, 3)] // 0b1100 <contiguous>
        [TestCase(13, 4, false, 0, 0)] // 0b1101
        [TestCase(14, 4, true, 1, 3)] // 0b1110 <contiguous>
        [TestCase(15, 4, true, 0, 3)] // 0b1110 <contiguous>
        public void FindContiguousBitMask(int valueDecRepr, int bitWidth, bool expectContiguousBitMask, int expectedStart, int expectedEnd)
        {
            Assert.IsTrue(expectedEnd >= expectedStart);
            var sb = GetSimpleBuilder();
            var constant = sb.ConstantBV(valueDecRepr, bitWidth);
            var cMask = ExprUtil.FindContiguousBitMask(constant);

            if (!expectContiguousBitMask)
                Assert.IsNull(cMask);
            else
            {
                Assert.IsNotNull(cMask);
                Assert.AreEqual(expectedStart, cMask.Item1);
                Assert.AreEqual(expectedEnd, cMask.Item2);
            }
        }
    }
}

