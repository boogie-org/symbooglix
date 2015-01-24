using System;
using NUnit.Framework;
using Microsoft.Boogie;
using Symbooglix;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class RealAndIntOperators
    {
        public RealAndIntOperators()
        {
            // This is a hack
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
        }

        private IExprBuilder GetBuilder()
        {
            return new SimpleExprBuilder();
        }

        private void CheckIsReal(Expr result)
        {
            Assert.IsTrue(result.ShallowType.IsReal);
            Assert.IsNotNull(result.Type);
            Assert.IsTrue(result.Type.IsReal);
        }

        private void CheckIsInt(Expr result)
        {
            Assert.IsTrue(result.ShallowType.IsInt);
            Assert.IsNotNull(result.Type);
            Assert.IsTrue(result.Type.IsInt);
        }

        // Add tests
        [Test()]
        public void AddReal()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Add(constant0, constant1);
            Assert.AreEqual("1e0 + 2e0", result.ToString());
            CheckIsReal(result);
        }

        [Test()]
        public void AddInt()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Add(constant0, constant1);
            Assert.AreEqual("1 + 2", result.ToString());
            CheckIsInt(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void AddLhsWrongType()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantReal("2.0");
            builder.Add(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void AddRhsWrongType()
        {
            var builder = GetBuilder();
            var constant1 = builder.ConstantInt(1);
            var constant0 = builder.ConstantReal("2.0");
            builder.Add(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void AddLhsRhsWrongType()
        {
            var builder = GetBuilder();
            var constant1 = builder.True;
            var constant0 = builder.False;
            builder.Add(constant0, constant1);
        }

        // Sub tests
        [Test()]
        public void SubReal()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Sub(constant0, constant1);
            Assert.AreEqual("1e0 - 2e0", result.ToString());
            CheckIsReal(result);
        }

        [Test()]
        public void SubInt()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Sub(constant0, constant1);
            Assert.AreEqual("1 - 2", result.ToString());
            CheckIsInt(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SubLhsWrongType()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantReal("2.0");
            builder.Sub(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SubRhsWrongType()
        {
            var builder = GetBuilder();
            var constant1 = builder.ConstantInt(1);
            var constant0 = builder.ConstantReal("2.0");
            builder.Sub(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SubLhsRhsWrongType()
        {
            var builder = GetBuilder();
            var constant1 = builder.True;
            var constant0 = builder.False;
            builder.Sub(constant0, constant1);
        }

        // Mul tests
        [Test()]
        public void MulReal()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Mul(constant0, constant1);
            Assert.AreEqual("1e0 * 2e0", result.ToString());
            CheckIsReal(result);
        }

        [Test()]
        public void MulInt()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Mul(constant0, constant1);
            Assert.AreEqual("1 * 2", result.ToString());
            CheckIsInt(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void MulLhsWrongType()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantReal("2.0");
            builder.Mul(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void MulRhsWrongType()
        {
            var builder = GetBuilder();
            var constant1 = builder.ConstantInt(1);
            var constant0 = builder.ConstantReal("2.0");
            builder.Mul(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void MulLhsRhsWrongType()
        {
            var builder = GetBuilder();
            var constant1 = builder.True;
            var constant0 = builder.False;
            builder.Mul(constant0, constant1);
        }
    }
}

