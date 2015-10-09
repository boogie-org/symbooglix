//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using NUnit.Framework;
using System;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class EqualityAndLogicalOperatorsSimpleBuilder : SimpleExprBuilderTestBase
    {
        [Test()]
        public void EqBool()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.True;
            var constant1 = builder.False;
            var result = builder.Eq(constant0, constant1);
            Assert.AreEqual("true == false", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void EqBv()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(2, 4);
            var result = builder.Eq(constant0, constant1);
            Assert.AreEqual("5bv4 == 2bv4", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void EqInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(5);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Eq(constant0, constant1);
            Assert.AreEqual("5 == 2", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void EqReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("5.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Eq(constant0, constant1);
            Assert.AreEqual("5e0 == 2e0", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void EqTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("5.0");
            var constant1 = builder.True;
            builder.Eq(constant0, constant1);
        }

        [Test()]
        public void NotEqBool()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.True;
            var constant1 = builder.False;
            var result = builder.NotEq(constant0, constant1);
            Assert.AreEqual("true != false", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void NotEqBv()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantBV(5, 4);
            var constant1 = builder.ConstantBV(2, 4);
            var result = builder.NotEq(constant0, constant1);
            Assert.AreEqual("5bv4 != 2bv4", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void NotEqInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(5);
            var constant1 = builder.ConstantInt(2);
            var result = builder.NotEq(constant0, constant1);
            Assert.AreEqual("5 != 2", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void NotEqReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("5.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.NotEq(constant0, constant1);
            Assert.AreEqual("5e0 != 2e0", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void NotEqTypeMismatch()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("5.0");
            var constant1 = builder.True;
            builder.NotEq(constant0, constant1);
        }

        [Test()]
        public void IfThenElseSimple()
        {
            var builder = GetSimpleBuilder();
            var condition = builder.False;
            var constant0 = builder.ConstantInt(5);
            var constant1 = builder.ConstantInt(2);
            var result = builder.IfThenElse(condition, constant0, constant1);
            Assert.AreEqual("(if false then 5 else 2)", result.ToString());
            Assert.IsNotNull(result.Type);
            Assert.IsTrue(result.Type.IsInt);
            Assert.IsTrue(result.ShallowType.IsInt);
            var TC = new TypecheckingContext(this);
            result.Typecheck(TC);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void IfThenElseTypeMistmatchCondition()
        {
            var builder = GetSimpleBuilder();
            var condition = builder.ConstantInt(0);
            var constant0 = builder.ConstantInt(5);
            var constant1 = builder.ConstantInt(2);
            builder.IfThenElse(condition, constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void IfThenElseTypeMistmatchThenElse()
        {
            var builder = GetSimpleBuilder();
            var condition = builder.False;
            var constant0 = builder.ConstantInt(5);
            var constant1 = builder.ConstantBV(5, 4);
            builder.IfThenElse(condition, constant0, constant1);
        }

        [Test()]
        public void Not()
        {
            var builder = GetSimpleBuilder();
            var condition = builder.False;
            var result = builder.Not(condition);
            Assert.AreEqual("!false", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(),ExpectedException(typeof(ExprTypeCheckException))]
        public void NotWrongType()
        {
            var builder = GetSimpleBuilder();
            var condition = builder.ConstantBV(2, 5);
            builder.Not(condition);
        }

        [Test()]
        public void And()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.True;
            var constant1 = builder.False;
            var result = builder.And(constant0, constant1);
            Assert.AreEqual("true && false", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void AndWrongLhsType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.True;
            var constant1 = builder.ConstantInt(8);
            builder.And(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void AndWrongRhsType()
        {
            var builder = GetSimpleBuilder();
            var constant1 = builder.True;
            var constant0 = builder.ConstantInt(8);
            builder.And(constant0, constant1);
        }

        [Test()]
        public void Or()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.True;
            var constant1 = builder.False;
            var result = builder.Or(constant0, constant1);
            Assert.AreEqual("true || false", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void OrWrongLhsType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.True;
            var constant1 = builder.ConstantInt(8);
            builder.Or(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void OrWrongRhsType()
        {
            var builder = GetSimpleBuilder();
            var constant1 = builder.True;
            var constant0 = builder.ConstantInt(8);
            builder.Or(constant0, constant1);
        }

        [Test()]
        public void Iff()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.True;
            var constant1 = builder.False;
            var result = builder.Iff(constant0, constant1);
            Assert.AreEqual("true <==> false", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void IffWrongLhsType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.True;
            var constant1 = builder.ConstantInt(8);
            builder.Iff(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void IffWrongRhsType()
        {
            var builder = GetSimpleBuilder();
            var constant1 = builder.True;
            var constant0 = builder.ConstantInt(8);
            builder.Iff(constant0, constant1);
        }

        [Test()]
        public void Imp()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.True;
            var constant1 = builder.False;
            var result = builder.Imp(constant0, constant1);
            Assert.AreEqual("true ==> false", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void ImpWrongLhsType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.True;
            var constant1 = builder.ConstantInt(8);
            builder.Imp(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void ImpWrongRhsType()
        {
            var builder = GetSimpleBuilder();
            var constant1 = builder.True;
            var constant0 = builder.ConstantInt(8);
            builder.Imp(constant0, constant1);
        }
    }
}

