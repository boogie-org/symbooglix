using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Symbooglix;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class Coercion
    {
        public Coercion()
        {
            // This is a hack
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();
        }

        private IExprBuilder GetBuilder()
        {
            return new SimpleExprBuilder();
        }

        private void CheckType(Expr result, Predicate<Microsoft.Boogie.Type> p)
        {
            Assert.IsTrue(p(result.ShallowType));
            Assert.IsNotNull(result.Type);
            Assert.IsTrue(p(result.Type));
        }

        [Test()]
        public void IntToRealCoercion()
        {
            var builder = GetBuilder();
            var constant = builder.ConstantInt(5);
            var result = builder.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToReal, constant);
            Assert.AreEqual("real(5)", result.ToString());
            CheckType(result, p => p.IsReal);
        }

        [Test()]
        public void RealToIntCoercion()
        {
            var builder = GetBuilder();
            var constant = builder.ConstantReal("5.0");
            var result = builder.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToInt, constant);
            Assert.AreEqual("int(5e0)", result.ToString());
            CheckType(result, p => p.IsInt);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void ToRealWrongOperandType()
        {
            var builder = GetBuilder();
            var constant = builder.ConstantReal("5.0");
            builder.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToReal, constant);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void ToIntWrongOperandType()
        {
            var builder = GetBuilder();
            var constant = builder.ConstantInt(5);
            builder.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToInt, constant);
        }
    }
}

