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

using BPLType = Microsoft.Boogie.Type;

namespace ExprBuilderTests
{
    public class BuilderDuplicatorTests : SimpleExprBuilderTestBase
    {
        private BuilderDuplicator GetDuplicator(IExprBuilder builder)
        {
            return new BuilderDuplicator(builder);
        }

        private void DuplicateAndCheck(Expr original, IExprBuilder builder)
        {
            var duplicator = GetDuplicator(builder);
            var copy = (Expr) duplicator.Visit(original);

            // Check they are structually equal
            Assert.IsTrue(original.Equals(copy));

            // Check the roots are different instances
            Assert.AreNotSame(original, copy);

            // Verify the nodes are disjoint, allow constants to be shared though
            var c = new DuplicationVerifier(/*ignoreDuplicateConstants=*/ true, /*ignoreDuplicateSymbolics=*/false);
            var sharedNodes = c.CheckDuplication(original, copy);
            Assert.AreEqual(0, sharedNodes.Count);

            // Verify all nodes are immutable
            var iv = new ImmutableExprVerifier();
            iv.Visit(copy);
            Assert.AreEqual(0, iv.NonImmutableNodes.Count);

            // Type check both Expr
            var TC = new TypecheckingContext(this);
            original.Typecheck(TC);
            copy.Typecheck(TC);
        }

        // Constants

        [TestCase(1, 8)]
        [TestCase(5, 16)]
        [TestCase(10, 64)]
        public void BitVectorConstant(int value, int width)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(value, width);
            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void IntConstant(int value)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantInt(value);
            DuplicateAndCheck(root, builder);
        }

        [TestCase("1.0")]
        [TestCase("5.75")]
        [TestCase("3.333")]
        public void RealConstant(string value)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantReal(value);
            DuplicateAndCheck(root, builder);
        }

        [TestCase(true)]
        [TestCase(false)]
        public void BoolConstant(bool value)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBool(value);
            DuplicateAndCheck(root, builder);
        }

        // Bitvector operators

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVAdd(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVADD(root , root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVADD8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVSub(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVSUB(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVSUB8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVMul(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVMUL(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVMUL8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVUdiv(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVUDIV(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVUDIV8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVSdiv(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVSDIV(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVSDIV8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVURem(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVUREM(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVUREM8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVSRem(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVSREM(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVSREM8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVSMod(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVSMOD(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVSMOD8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVSHL(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVSHL(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVSHL8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVLSHR(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVLSHR(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVLSHR8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVASHR(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVASHR(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVASHR8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVAND(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVAND(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVAND8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVOR(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVOR(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVOR8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVXOR(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build symmetric Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVXOR(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVXOR8(1bv8, 1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleBVSLT()
        {
            var builder = GetSimpleBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVSLT(lhs, rhs);

            Assert.AreEqual("BVSLT8(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleBVSLE()
        {
            var builder = GetSimpleBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVSLE(lhs, rhs);

            Assert.AreEqual("BVSLE8(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleBVSGT()
        {
            var builder = GetSimpleBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVSGT(lhs, rhs);

            Assert.AreEqual("BVSGT8(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleBVSGE()
        {
            var builder = GetSimpleBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVSGE(lhs, rhs);

            Assert.AreEqual("BVSGE8(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleBVULT()
        {
            var builder = GetSimpleBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVULT(lhs, rhs);

            Assert.AreEqual("BVULT8(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleBVULE()
        {
            var builder = GetSimpleBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVULE(lhs, rhs);

            Assert.AreEqual("BVULE8(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleBVUGT()
        {
            var builder = GetSimpleBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVUGT(lhs, rhs);

            Assert.AreEqual("BVUGT8(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        public void simpleBVUGE()
        {
            var builder = GetSimpleBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVSGE(lhs, rhs);

            Assert.AreEqual("BVUGE8(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVNOT(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVNOT(root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVNOT8(1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVNEG(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.BVNEG(root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("BVNEG8(1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVSEXT(int width)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build Expr Tree
            for (int count = 1; count <= width; ++count)
            {
                root = builder.BVSEXT(root, 8 + count);
            }

            if (width == 1)
            {
                Assert.AreEqual("BV8_SEXT9(1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVZEXT(int width)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build Expr Tree
            for (int count = 1; count <= width; ++count)
            {
                root = builder.BVZEXT(root, 8 + count);
            }

            if (width == 1)
            {
                Assert.AreEqual("BV8_ZEXT9(1bv8)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [Ignore("FIXME: Boogie's type checker tries to change the type of immutable Expr")]
        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVCONCAT(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 8);

            // Build Expr Tree
            for (int count = 1; count <= repeat; ++count)
            {
                root = builder.BVCONCAT(root, root);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("1bv8 ++ 1bv8", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVEXTRACT(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(1, 128);

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.BVEXTRACT(root, 128 - count, 0);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("1bv128[128:0]", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        // Int/Real operators

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleAdd(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantInt(1);

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.Add(root, root);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("1 + 1", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleSub(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantInt(1);

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.Sub(root, root);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("1 - 1", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleMul(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantInt(1);

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.Mul(root, root);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("1 * 1", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleMod(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantInt(1);

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.Mod(root, root);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("1 mod 1", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleDiv(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantInt(1);

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.Div(root, root);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("1 div 1", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleRealDiv(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantReal("1.0");

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.RealDiv(root, root);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("1e0 / 1e0", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simplePow(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantReal("1.0");

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.Pow(root, root);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("1e0 ** 1e0", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleNeg(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantInt(1);

            // Build Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.Neg(root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("-1", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleArithmeticCoercion(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantInt(1);

            // Build Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                if (count % 2 == 0)
                    root = builder.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToReal, root);
                else
                    root = builder.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToInt, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("real(1)", root.ToString());
            }
            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleAnd(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.True;

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.And(root, root);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("true && true", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleOr(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.True;

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.Or(root, root);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("true || true", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleIff(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.True;

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.Iff(root, root);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("true <==> true", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleImp(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.True;

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.Imp(root, root);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("true ==> true", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleIfThenElse(int repeat)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.True;

            // Build Expr Tree
            for (int count = 0; count < repeat; ++count)
            {
                root = builder.IfThenElse(root, root, builder.False);
            }

            if (repeat == 1)
            {
                Assert.AreEqual("(if true then true else false)", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleNot(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.True;

            // Build Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.Not(root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("!true", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleEq(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.True;

            // Build Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.Eq(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("true == true", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleNotEq(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.True;

            // Build Expr Tree
            for (int count = 0; count < depth; ++count)
            {
                root = builder.NotEq(root, root);
            }

            if (depth == 1)
            {
                Assert.AreEqual("true != true", root.ToString());
            }

            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleLt()
        {
            var builder = GetSimpleBuilder();

            // Build Expr Tree
            var root = builder.Lt(builder.ConstantInt(0), builder.ConstantInt(1));
            Assert.AreEqual("0 < 1", root.ToString());

            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleLe()
        {
            var builder = GetSimpleBuilder();

            // Build Expr Tree
            var root = builder.Le(builder.ConstantInt(0), builder.ConstantInt(1));
            Assert.AreEqual("0 <= 1", root.ToString());

            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleGt()
        {
            var builder = GetSimpleBuilder();

            // Build Expr Tree
            var root = builder.Gt(builder.ConstantInt(0), builder.ConstantInt(1));
            Assert.AreEqual("0 > 1", root.ToString());

            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleGe()
        {
            var builder = GetSimpleBuilder();

            // Build Expr Tree
            var root = builder.Ge(builder.ConstantInt(0), builder.ConstantInt(1));
            Assert.AreEqual("0 >= 1", root.ToString());

            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleUF()
        {
            var builder = GetSimpleBuilder();
            var FCB = new FunctionCallBuilder();
            var func = FCB.CreateUninterpretedFunctionCall("foo", BasicType.Bool, new List<Microsoft.Boogie.Type>() {
                BasicType.Real,
                BasicType.Int,
                BasicType.GetBvType(8)
            });
            var root = builder.UFC(func, builder.ConstantReal("0.0"), builder.ConstantInt(5), builder.ConstantBV(5,8));
            Assert.AreEqual("foo(0e0, 5, 5bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleMapSelect()
        {
            var builder = GetSimpleBuilder();
            var map = GetMapVariable("m", BasicType.Bool, BasicType.Int, BasicType.Int).Item1;
            var root = builder.MapSelect(map, builder.ConstantInt(0), builder.ConstantInt(1));
            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(2)]
        [TestCase(10)]
        public void simpleMapStore(int depth)
        {
            var builder = GetSimpleBuilder();
            var map = GetMapVariable("m", BasicType.Bool, BasicType.Int).Item1;
            Expr root = map;

            for (int count = 0; count < depth; ++count)
            {
                root =  builder.MapStore(root, builder.True, builder.ConstantInt(count));
            }
            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(2)]
        [TestCase(10)]
        public void simpleOld(int depth)
        {
            var builder = GetSimpleBuilder();
            Expr root = builder.ConstantBV(0, 8);

            for (int count = 0; count < depth; ++count)
            {
                root = builder.Old(root);
            }
            DuplicateAndCheck(root, builder);
        }



        [Test()]
        public void simpleExists()
        {
            var builder = GetSimpleBuilder();
            var free0Pair = GetVarAndIdExpr("x", BasicType.Int);
            var free1Pair = GetVarAndIdExpr("y", BasicType.Int);
            Variable free0Var = free0Pair.Item1;
            Variable free1Var = free1Pair.Item1;
            IdentifierExpr x = free0Pair.Item2;
            IdentifierExpr y = free1Pair.Item2;

            var root = builder.Exists(new List<Variable>() { free0Var, free1Var },
                builder.Gt(builder.Add(x, y),
                           builder.Sub(x, y)));
            Assert.AreEqual("(exists x: int, y: int :: x + y > x - y)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleExistsWithTrigger()
        {
            var builder = GetSimpleBuilder();
            var free0Pair = GetVarAndIdExpr("x", BasicType.Int);
            var free1Pair = GetVarAndIdExpr("y", BasicType.Int);
            Variable free0Var = free0Pair.Item1;
            Variable free1Var = free1Pair.Item1;
            IdentifierExpr x = free0Pair.Item2;
            IdentifierExpr y = free1Pair.Item2;

            var fb = new FunctionCallBuilder();
            var dummyFunc = fb.CreateCachedUninterpretedFunctionCall("f", BPLType.Bool,
                new List<BPLType>() {BPLType.Int, BPLType.Int});

            var triggerExpr = builder.UFC(dummyFunc, x, y);
            var trigger = new Trigger(Token.NoToken,
                /*pos=*/true,
                new List<Expr>() { triggerExpr },
                null);

            var root = builder.Exists(new List<Variable>() { free0Var, free1Var },
                builder.Gt(builder.Add(x, y),
                    builder.Sub(x, y)), trigger);
            Assert.AreEqual("(exists x: int, y: int :: { f(x, y) } x + y > x - y)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleForall()
        {
            var builder = GetSimpleBuilder();
            var free0Pair = GetVarAndIdExpr("x", BasicType.Int);
            var free1Pair = GetVarAndIdExpr("y", BasicType.Int);
            Variable free0Var = free0Pair.Item1;
            Variable free1Var = free1Pair.Item1;
            IdentifierExpr x = free0Pair.Item2;
            IdentifierExpr y = free1Pair.Item2;

            var root = builder.ForAll(new List<Variable>() { free0Var, free1Var },
                builder.Gt(builder.Add(x, y),
                           builder.Sub(x, y)));
            Assert.AreEqual("(forall x: int, y: int :: x + y > x - y)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        [Test()]
        public void simpleForallWithTrigger()
        {
            var builder = GetSimpleBuilder();
            var free0Pair = GetVarAndIdExpr("x", BasicType.Int);
            var free1Pair = GetVarAndIdExpr("y", BasicType.Int);
            Variable free0Var = free0Pair.Item1;
            Variable free1Var = free1Pair.Item1;
            IdentifierExpr x = free0Pair.Item2;
            IdentifierExpr y = free1Pair.Item2;

            var fb = new FunctionCallBuilder();
            var dummyFunc = fb.CreateCachedUninterpretedFunctionCall("f", BPLType.Bool,
                new List<BPLType>() {BPLType.Int, BPLType.Int});

            var triggerExpr = builder.UFC(dummyFunc, x, y);
            var trigger = new Trigger(Token.NoToken,
                /*pos=*/true,
                new List<Expr>() { triggerExpr },
                null);

            var root = builder.ForAll(new List<Variable>() { free0Var, free1Var },
                builder.Gt(builder.Add(x, y),
                    builder.Sub(x, y)), trigger);
            Assert.AreEqual("(forall x: int, y: int :: { f(x, y) } x + y > x - y)", root.ToString());
            DuplicateAndCheck(root, builder);
        }
    }
}

