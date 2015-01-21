using NUnit.Framework;
using System;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class EqualityAndLogicalOperators
    {
        public EqualityAndLogicalOperators ()
        {
            // This is a hack
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
        }

        private IExprBuilder GetBuilder()
        {
            return new SimpleExprBuilder();
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

        [Test()]
        public void EqBool()
        {
            var builder = GetBuilder();
            var constant0 = builder.True;
            var constant1 = builder.False;
            var result = builder.Eq(constant0, constant1);
            Assert.AreEqual("true == false", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void EqBv()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(2, 4);
            var result = builder.Eq(constant0, constant1);
            Assert.AreEqual("5bv4 == 2bv4", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void EqInt()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantInt(5);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Eq(constant0, constant1);
            Assert.AreEqual("5 == 2", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void EqReal()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantReal("5.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Eq(constant0, constant1);
            Assert.AreEqual("5e0 == 2e0", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void EqTypeMismatch()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantReal("5.0");
            var constant1 = builder.True;
            builder.Eq(constant0, constant1);
        }

        [Test()]
        public void NotEqBool()
        {
            var builder = GetBuilder();
            var constant0 = builder.True;
            var constant1 = builder.False;
            var result = builder.NotEq(constant0, constant1);
            Assert.AreEqual("true != false", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void NotEqBv()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(2, 4);
            var result = builder.NotEq(constant0, constant1);
            Assert.AreEqual("5bv4 != 2bv4", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void NotEqInt()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantInt(5);
            var constant1 = builder.ConstantInt(2);
            var result = builder.NotEq(constant0, constant1);
            Assert.AreEqual("5 != 2", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void NotEqReal()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantReal("5.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.NotEq(constant0, constant1);
            Assert.AreEqual("5e0 != 2e0", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void NotEqTypeMismatch()
        {
            var builder = GetBuilder();
            var constant0 = builder.ConstantReal("5.0");
            var constant1 = builder.True;
            builder.NotEq(constant0, constant1);
        }

        [Test()]
        public void IfThenElseSimple()
        {
            var builder = GetBuilder();
            var condition = builder.False;
            var constant0 = builder.ConstantInt(5);
            var constant1 = builder.ConstantInt(2);
            var result = builder.IfThenElse(condition, constant0, constant1);
            Assert.AreEqual("(if false then 5 else 2)", result.ToString());
            Assert.IsNotNull(result.Type);
            Assert.IsTrue(result.Type.IsInt);
            Assert.IsTrue(result.ShallowType.IsInt);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void IfThenElseTypeMistmatchCondition()
        {
            var builder = GetBuilder();
            var condition = builder.ConstantInt(0);
            var constant0 = builder.ConstantInt(5);
            var constant1 = builder.ConstantInt(2);
            builder.IfThenElse(condition, constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void IfThenElseTypeMistmatchThenElse()
        {
            var builder = GetBuilder();
            var condition = builder.False;
            var constant0 = builder.ConstantInt(5);
            var constant1 = builder.ConstantBV(5, 4);
            builder.IfThenElse(condition, constant0, constant1);
        }

        [Test()]
        public void Not()
        {
            var builder = GetBuilder();
            var condition = builder.False;
            var result = builder.Not(condition);
            Assert.AreEqual("!false", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void NotWrongType()
        {
            var builder = GetBuilder();
            var condition = builder.ConstantBV(2, 5);
            builder.Not(condition);
        }
    }
}

