//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using Microsoft.Boogie;
using System;
using Symbooglix;
using SymbooglixLibTests;
using NUnit.Framework;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class BVOperatorsSimplerBuilder : SimpleExprBuilderTestBase
    {
        [Test()]
        public void Bvslt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVSLT(constant0, constant1);
            Assert.AreEqual("BVSLT4(5bv4, 11bv4)", result.ToString());
            CheckIsBoolType(result);
            CheckBvBuiltIn(result, "bvslt");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvsltTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSLT(constant0, constant1);
        }

        // FIXME: We should test this for all bitvector operators. I'm being lazy here
        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvsltWrongLhsType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.True;
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSLT(constant0, constant1);
        }

        // FIXME: We should test this for all bitvector operators. I'm being lazy here
        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvsltWrongRhsType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 5);
            var constant1 = builder.True;
            builder.BVSLT(constant0, constant1);
        }

        [Test()]
        public void Bvsle()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVSLE(constant0, constant1);
            Assert.AreEqual("BVSLE4(5bv4, 11bv4)", result.ToString());
            CheckIsBoolType(result);
            CheckBvBuiltIn(result, "bvsle");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvsleTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSLE(constant0, constant1);
        }

        [Test()]
        public void Bvsgt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVSGT(constant0, constant1);
            Assert.AreEqual("BVSGT4(5bv4, 11bv4)", result.ToString());
            CheckIsBoolType(result);
            CheckBvBuiltIn(result, "bvsgt");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvsgtTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSGT(constant0, constant1);
        }

        [Test()]
        public void Bvsge()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVSGE(constant0, constant1);
            Assert.AreEqual("BVSGE4(5bv4, 11bv4)", result.ToString());
            CheckIsBoolType(result);
            CheckBvBuiltIn(result, "bvsge");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvsgeTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSGE(constant0, constant1);
        }

        [Test()]
        public void Bvult()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVULT(constant0, constant1);
            Assert.AreEqual("BVULT4(5bv4, 11bv4)", result.ToString());
            CheckIsBoolType(result);
            CheckBvBuiltIn(result, "bvult");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvultTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVULT(constant0, constant1);
        }

        [Test()]
        public void Bvule()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVULE(constant0, constant1);
            Assert.AreEqual("BVULE4(5bv4, 11bv4)", result.ToString());
            CheckIsBoolType(result);
            CheckBvBuiltIn(result, "bvule");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvuleTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVULE(constant0, constant1);
        }

        [Test()]
        public void Bvugt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVUGT(constant0, constant1);
            Assert.AreEqual("BVUGT4(5bv4, 11bv4)", result.ToString());
            CheckIsBoolType(result);
            CheckBvBuiltIn(result, "bvugt");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvugtTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVUGT(constant0, constant1);
        }

        [Test()]
        public void Bvuge()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVUGE(constant0, constant1);
            Assert.AreEqual("BVUGE4(5bv4, 11bv4)", result.ToString());
            CheckIsBoolType(result);
            CheckBvBuiltIn(result, "bvuge");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvugeTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVUGE(constant0, constant1);
        }

        [Test()]
        public void Bvand()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVAND(constant0, constant1);
            Assert.AreEqual("BVAND4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvand");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvandTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVAND(constant0, constant1);
        }

        [Test()]
        public void Bvor()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVOR(constant0, constant1);
            Assert.AreEqual("BVOR4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvor");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvorTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVOR(constant0, constant1);
        }

        [Test()]
        public void Bvxor()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVXOR(constant0, constant1);
            Assert.AreEqual("BVXOR4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvxor");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvxorTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVXOR(constant0, constant1);
        }

        [Test()]
        public void Bvshl()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVSHL(constant0, constant1);
            Assert.AreEqual("BVSHL4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvshl");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvshlTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSHL(constant0, constant1);
        }

        [Test()]
        public void Bvlshr()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVLSHR(constant0, constant1);
            Assert.AreEqual("BVLSHR4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvlshr");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvlshrTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVLSHR(constant0, constant1);
        }

        [Test()]
        public void Bvashr()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVASHR(constant0, constant1);
            Assert.AreEqual("BVASHR4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvashr");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvashrTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVASHR(constant0, constant1);
        }

        [Test()]
        public void Bvadd()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVADD(constant0, constant1);
            Assert.AreEqual("BVADD4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvadd");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvaddTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVADD(constant0, constant1);
        }

        [Test()]
        public void Bvsub()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVSUB(constant0, constant1);
            Assert.AreEqual("BVSUB4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvsub");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvsubTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSUB(constant0, constant1);
        }

        [Test()]
        public void Bvmul()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVMUL(constant0, constant1);
            Assert.AreEqual("BVMUL4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvmul");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvmulTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVMUL(constant0, constant1);
        }

        [Test()]
        public void Bvudiv()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVUDIV(constant0, constant1);
            Assert.AreEqual("BVUDIV4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvudiv");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvudivTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVUDIV(constant0, constant1);
        }

        [Test()]
        public void Bvurem()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVUREM(constant0, constant1);
            Assert.AreEqual("BVUREM4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvurem");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvuremTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVUREM(constant0, constant1);
        }

        [Test()]
        public void Bvsdiv()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVSDIV(constant0, constant1);
            Assert.AreEqual("BVSDIV4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvsdiv");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvsdivTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSDIV(constant0, constant1);
        }

        [Test()]
        public void Bvsrem()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVSREM(constant0, constant1);
            Assert.AreEqual("BVSREM4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvsrem");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvsremTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSREM(constant0, constant1);
        }

        [Test()]
        public void Bvsmod()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 4);
            var result = builder.BVSMOD(constant0, constant1);
            Assert.AreEqual("BVSMOD4(5bv4, 11bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvsmod");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvsmodTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSMOD(constant0, constant1);
        }

        [Test()]
        public void Bvneg()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var result = builder.BVNEG(constant0);
            Assert.AreEqual("BVNEG4(5bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvneg");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvnegTypeError()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.False;
            builder.BVNEG(constant0);
        }

        [Test()]
        public void Bvnot()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var result = builder.BVNOT(constant0);
            Assert.AreEqual("BVNOT4(5bv4)", result.ToString());
            CheckIsBvType(result, 4);
            CheckBvBuiltIn(result, "bvnot");
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvnotTypeError()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.False;
            builder.BVNOT(constant0);
        }

        [Test()]
        public void Bvsext()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var result = builder.BVSEXT(constant0, 5);
            Assert.AreEqual("BV4_SEXT5(5bv4)", result.ToString());
            CheckIsBvType(result, 5);
            CheckBvBuiltIn(result, "sign_extend 1");
        }

        [Test(),ExpectedException(typeof(ArgumentException))]
        public void BvsextWrongWidth()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            builder.BVSEXT(constant0, 3);
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvsextWrongType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.False;
            builder.BVSEXT(constant0, 3);
        }

        [Test()]
        public void Bvzext()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var result = builder.BVZEXT(constant0, 5);
            Assert.AreEqual("BV4_ZEXT5(5bv4)", result.ToString());
            CheckIsBvType(result, 5);
            CheckBvBuiltIn(result, "zero_extend 1");
        }

        [Test(),ExpectedException(typeof(ArgumentException))]
        public void BvzextWrongWidth()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            builder.BVZEXT(constant0, 3);
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void BvzextWrongType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.False;
            builder.BVZEXT(constant0, 3);
        }

        [Test(), Ignore("FIXME: Boogie's type checker tries to change the type of immutable Expr")]
        public void Bvconcat()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            var result = builder.BVCONCAT(constant1, constant0);
            Assert.AreEqual("11bv5 ++ 5bv4", result.ToString());
            CheckIsBvType(result, 9);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void BvconcatWrongMSBType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.True;
            builder.BVCONCAT(constant1, constant0);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void BvconcatWrongLSBType()
        {
            var builder = GetSimpleBuilder();
            var constant1 = builder.ConstantBV(5, 4);
            var constant0 = builder.True;
            builder.BVCONCAT(constant1, constant0);
        }

        [Test()]
        public void Bvextract()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var result = builder.BVEXTRACT(constant0, 2, 0);
            Assert.AreEqual("5bv4[2:0]", result.ToString());
            CheckIsBvType(result, 2);
        }

        [Test(), ExpectedException(typeof(ArgumentException))]
        public void BvextractInvalidRange()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            builder.BVEXTRACT(constant0, 0, 0);
        }

        [Test(), ExpectedException(typeof(ArgumentException))]
        public void BvextractInvalidRange2()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            builder.BVEXTRACT(constant0, 3, -2);
        }

        [Test()]
        public void BvextractValidRangeOnEdge()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            // [4:2] means bits (4,2] i.e. bits 3 and 2
            builder.BVEXTRACT(constant0, 4, 2);
        }

        [Test(), ExpectedException(typeof(ArgumentException))]
        public void BvextractInvalidRange3()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            builder.BVEXTRACT(constant0, 5, 2);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void BvextractInvalidType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.True;
            builder.BVEXTRACT(constant0, 3, 0);
        }
    }
}

