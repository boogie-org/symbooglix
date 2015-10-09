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
using Microsoft.Boogie;
using Symbooglix;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class CoercionSimpleBuilder : SimpleExprBuilderTestBase
    {
        // Arithmetic Coercion

        [Test()]
        public void IntToRealCoercion()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantInt(5);
            var result = builder.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToReal, constant);
            Assert.AreEqual("real(5)", result.ToString());
            CheckType(result, p => p.IsReal);
        }

        [Test()]
        public void RealToIntCoercion()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantReal("5.0");
            var result = builder.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToInt, constant);
            Assert.AreEqual("int(5e0)", result.ToString());
            CheckType(result, p => p.IsInt);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void ToRealWrongOperandType()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantReal("5.0");
            builder.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToReal, constant);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void ToIntWrongOperandType()
        {
            var builder = GetSimpleBuilder();
            var constant = builder.ConstantInt(5);
            builder.ArithmeticCoercion(ArithmeticCoercion.CoercionType.ToInt, constant);
        }
    }
}

