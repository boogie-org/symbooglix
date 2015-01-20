using Microsoft.Boogie;
using System;
using Symbooglix;
using SymbooglixLibTests;
using NUnit.Framework;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class BVOperators
    {
        public BVOperators()
        {
            // This is a hack
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();

            SymbooglixLibTests.SymbooglixTest.SetupDebug();
        }

        public IExprBuilder GetBuilder()
        {
            return new SimpleExprBuilder();
        }

        private void CheckBvBuiltIn(Expr e, string expected)
        {
            Assert.IsInstanceOf<NAryExpr>(e);
            var asNary = e as NAryExpr;
            Assert.IsInstanceOf<FunctionCall>(asNary.Fun);
            var fc = asNary.Fun as FunctionCall;
            var actual = QKeyValue.FindStringAttribute(fc.Func.Attributes, "bvbuiltin");
            Assert.IsNotNullOrEmpty(actual);
            Assert.AreEqual(expected, actual);
        }

        private void CheckIsBoolType(Expr result)
        {
            var shallowType = result.ShallowType;
            Assert.IsNotNull(shallowType);
            Assert.IsTrue(shallowType.IsBool);
            var t = result.Type;
            Assert.IsNotNull(t);
            Assert.IsTrue(t.IsBool);
        }

        private void CheckIsBvType(Expr result, int width)
        {
            var shallowType = result.ShallowType;
            Assert.IsNotNull(shallowType);
            Assert.IsTrue(shallowType.IsBv);
            Assert.AreEqual(width, shallowType.BvBits);
            var t = result.Type;
            Assert.IsNotNull(t);
            Assert.IsTrue(t.IsBv);
            Assert.AreEqual(width, t.BvBits);
        }

        [Test()]
        public void Bvslt()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSLT(constant0, constant1);
        }

        [Test()]
        public void Bvsle()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSLE(constant0, constant1);
        }

        [Test()]
        public void Bvsgt()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSGT(constant0, constant1);
        }

        [Test()]
        public void Bvsge()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSGE(constant0, constant1);
        }

        [Test()]
        public void Bvult()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVULT(constant0, constant1);
        }

        [Test()]
        public void Bvule()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVULE(constant0, constant1);
        }

        [Test()]
        public void Bvugt()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVUGT(constant0, constant1);
        }

        [Test()]
        public void Bvuge()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVUGE(constant0, constant1);
        }

        [Test()]
        public void Bvand()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVAND(constant0, constant1);
        }

        [Test()]
        public void Bvor()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVOR(constant0, constant1);
        }

        [Test()]
        public void Bvxor()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVXOR(constant0, constant1);
        }

        [Test()]
        public void Bvshl()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSHL(constant0, constant1);
        }

        [Test()]
        public void Bvlshr()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVLSHR(constant0, constant1);
        }

        [Test()]
        public void Bvashr()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVASHR(constant0, constant1);
        }

        [Test()]
        public void Bvadd()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVADD(constant0, constant1);
        }

        [Test()]
        public void Bvmul()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVMUL(constant0, constant1);
        }

        [Test()]
        public void Bvudiv()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVUDIV(constant0, constant1);
        }

        [Test()]
        public void Bvurem()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVUREM(constant0, constant1);
        }

        [Test()]
        public void Bvsdiv()
        {
            var builder = GetBuilder();
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
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(11, 5);
            builder.BVSDIV(constant0, constant1);
        }
    }
}

