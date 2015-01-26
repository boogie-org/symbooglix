using System;
using System.Collections;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

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

            // Type check both Expr
            var TC = new TypecheckingContext(this);
            original.Typecheck(TC);
            copy.Typecheck(TC);
        }

        [TestCase(1, 8)]
        [TestCase(5, 16)]
        [TestCase(10, 64)]
        public void BitVectorConstant(int value, int width)
        {
            var builder = GetBuilder();
            Expr root = builder.ConstantBV(value, width);
            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void IntConstant(int value)
        {
            var builder = GetBuilder();
            Expr root = builder.ConstantInt(value);
            DuplicateAndCheck(root, builder);
        }

        [TestCase("1.0")]
        [TestCase("5.75")]
        [TestCase("3.333")]
        public void RealConstant(string value)
        {
            var builder = GetBuilder();
            Expr root = builder.ConstantReal(value);
            DuplicateAndCheck(root, builder);
        }

        [TestCase(true)]
        [TestCase(false)]
        public void BoolConstant(bool value)
        {
            var builder = GetBuilder();
            Expr root = builder.ConstantBool(value);
            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVAdd(int depth)
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            
        public void simpleBVSLT()
        {
            var builder = GetBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVSLT(lhs, rhs);

            Assert.AreEqual("BVSLT(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        public void simpleBVSLE()
        {
            var builder = GetBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVSLE(lhs, rhs);

            Assert.AreEqual("BVSLE(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        public void simpleBVSGT()
        {
            var builder = GetBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVSGT(lhs, rhs);

            Assert.AreEqual("BVSGT(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        public void simpleBVSGE()
        {
            var builder = GetBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVSGE(lhs, rhs);

            Assert.AreEqual("BVSGE(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }


        public void simpleBVULT()
        {
            var builder = GetBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVULT(lhs, rhs);

            Assert.AreEqual("BVULT(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        public void simpleBVULE()
        {
            var builder = GetBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVULE(lhs, rhs);

            Assert.AreEqual("BVULE(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        public void simpleBVUGT()
        {
            var builder = GetBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVUGT(lhs, rhs);

            Assert.AreEqual("BVUGT(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        public void simpleBVUGE()
        {
            var builder = GetBuilder();
            Expr lhs = builder.ConstantBV(1, 8);
            Expr rhs = builder.ConstantBV(2, 8);

            var root = builder.BVSGE(lhs, rhs);

            Assert.AreEqual("BVUGE(1bv8, 2bv8)", root.ToString());
            DuplicateAndCheck(root, builder);
        }

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVNOT(int depth)
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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

        [TestCase(1)]
        [TestCase(5)]
        [TestCase(10)]
        public void simpleBVCONCAT(int repeat)
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
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
    }
}

