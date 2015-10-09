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
using NUnit.Framework;
using Microsoft.Boogie;
using Symbooglix;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class RealAndIntOperatorsSimplerBuilder : SimpleExprBuilderTestBase
    {
        // Add tests
        [Test()]
        public void AddReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Add(constant0, constant1);
            Assert.AreEqual("1e0 + 2e0", result.ToString());
            CheckIsReal(result);
        }

        [Test()]
        public void AddInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Add(constant0, constant1);
            Assert.AreEqual("1 + 2", result.ToString());
            CheckIsInt(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void AddLhsWrongType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantReal("2.0");
            builder.Add(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void AddRhsWrongType()
        {
            var builder = GetSimpleBuilder();
            var constant1 = builder.ConstantInt(1);
            var constant0 = builder.ConstantReal("2.0");
            builder.Add(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void AddLhsRhsWrongType()
        {
            var builder = GetSimpleBuilder();
            var constant1 = builder.True;
            var constant0 = builder.False;
            builder.Add(constant0, constant1);
        }

        // Sub tests
        [Test()]
        public void SubReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Sub(constant0, constant1);
            Assert.AreEqual("1e0 - 2e0", result.ToString());
            CheckIsReal(result);
        }

        [Test()]
        public void SubInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Sub(constant0, constant1);
            Assert.AreEqual("1 - 2", result.ToString());
            CheckIsInt(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SubLhsWrongType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantReal("2.0");
            builder.Sub(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SubRhsWrongType()
        {
            var builder = GetSimpleBuilder();
            var constant1 = builder.ConstantInt(1);
            var constant0 = builder.ConstantReal("2.0");
            builder.Sub(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SubLhsRhsWrongType()
        {
            var builder = GetSimpleBuilder();
            var constant1 = builder.True;
            var constant0 = builder.False;
            builder.Sub(constant0, constant1);
        }

        // Mul tests
        [Test()]
        public void MulReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Mul(constant0, constant1);
            Assert.AreEqual("1e0 * 2e0", result.ToString());
            CheckIsReal(result);
        }

        [Test()]
        public void MulInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Mul(constant0, constant1);
            Assert.AreEqual("1 * 2", result.ToString());
            CheckIsInt(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void MulLhsWrongType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantReal("2.0");
            builder.Mul(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void MulRhsWrongType()
        {
            var builder = GetSimpleBuilder();
            var constant1 = builder.ConstantInt(1);
            var constant0 = builder.ConstantReal("2.0");
            builder.Mul(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void MulLhsRhsWrongType()
        {
            var builder = GetSimpleBuilder();
            var constant1 = builder.True;
            var constant0 = builder.False;
            builder.Mul(constant0, constant1);
        }

        // Div tests
        [Test()]
        public void DivInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Div(constant0, constant1);
            Assert.AreEqual("1 div 2", result.ToString());
            CheckIsInt(result);
        }

        // Note Div can't take real operands
        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void DivReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            builder.Div(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void DivMismatchArgTypes()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.False;
            builder.Div(constant0, constant1);
        }

        // RealDiv tests
        [Test()]
        public void RealDivIntArgs()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.RealDiv(constant0, constant1);
            Assert.AreEqual("1 / 2", result.ToString());
            CheckIsReal(result);
        }

        [Test()]
        public void RealDivRealArgs()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.RealDiv(constant0, constant1);
            Assert.AreEqual("1e0 / 2e0", result.ToString());
            CheckIsReal(result);
        }

        [Test()]
        public void RealDivMixedIntRealArgs()
        {
            var builder = GetSimpleBuilder();
            var constant1 = builder.ConstantReal("1.0");
            var constant0 = builder.ConstantInt(2);
            var result = builder.RealDiv(constant0, constant1);
            Assert.AreEqual("2 / 1e0", result.ToString());
            CheckIsReal(result);
        }

        [Test()]
        public void RealDivMixedRealIntArgs()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantInt(2);
            var result = builder.RealDiv(constant0, constant1);
            Assert.AreEqual("1e0 / 2", result.ToString());
            CheckIsReal(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void RealDivWrongArgTypes()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.False;
            var result = builder.RealDiv(constant0, constant1);
            Assert.AreEqual("1e0 / 2e0", result.ToString());
            CheckIsReal(result);
        }

        // Mod tests
        [Test()]
        public void ModInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Mod(constant0, constant1);
            Assert.AreEqual("1 mod 2", result.ToString());
            CheckIsInt(result);
        }

        // Note mod can't take real operands
        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void ModReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            builder.Mod(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void ModMismatchArgTypes()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.False;
            builder.Mod(constant0, constant1);
        }

        // Rem tests
        [Test()]
        public void RemInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Rem(constant0, constant1);
            Assert.AreEqual("rem(1, 2)", result.ToString());
            CheckBuiltIn(result, "rem");
            CheckIsInt(result);
        }

        // Note mod can't take real operands
        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void RemReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            builder.Rem(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void RemMismatchArgTypes()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.False;
            builder.Rem(constant0, constant1);
        }

        // Pow tests
        [Test()]
        public void PowReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Pow(constant0, constant1);
            Assert.AreEqual("1e0 ** 2e0", result.ToString());
            CheckIsReal(result);
        }

        // Note Pow can't take int operands
        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void PowInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            builder.Pow(constant0, constant1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void PowMismatchArgTypes()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.False;
            builder.Pow(constant0, constant1);
        }

        // Neg tests
        [Test()]
        public void NegInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var result = builder.Neg(constant0);
            Assert.AreEqual("-1", result.ToString());
            CheckIsInt(result);
        }

        [Test()]
        public void NegReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var result = builder.Neg(constant0);
            Assert.AreEqual("-1e0", result.ToString());
            CheckIsReal(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void NegWrongType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.False;
            builder.Neg(constant0);
        }

        // Lt tests
        [Test()]
        public void LtReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Lt(constant0, constant1);
            Assert.AreEqual("1e0 < 2e0", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void LtInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Lt(constant0, constant1);
            Assert.AreEqual("1 < 2", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void LtIntWrongArgType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.False;
            var constant1 = builder.True;
            builder.Lt(constant0, constant1);
        }

        // Le tests
        [Test()]
        public void LeReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Le(constant0, constant1);
            Assert.AreEqual("1e0 <= 2e0", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void LeInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Le(constant0, constant1);
            Assert.AreEqual("1 <= 2", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void LeIntWrongArgType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.False;
            var constant1 = builder.True;
            builder.Le(constant0, constant1);
        }

        // Gt tests
        [Test()]
        public void GtReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Gt(constant0, constant1);
            Assert.AreEqual("1e0 > 2e0", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void GtInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Gt(constant0, constant1);
            Assert.AreEqual("1 > 2", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void GtIntWrongArgType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.False;
            var constant1 = builder.True;
            builder.Gt(constant0, constant1);
        }

        // Ge tests
        [Test()]
        public void GeReal()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantReal("1.0");
            var constant1 = builder.ConstantReal("2.0");
            var result = builder.Ge(constant0, constant1);
            Assert.AreEqual("1e0 >= 2e0", result.ToString());
            CheckIsBoolType(result);
        }

        [Test()]
        public void GeInt()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.ConstantInt(1);
            var constant1 = builder.ConstantInt(2);
            var result = builder.Ge(constant0, constant1);
            Assert.AreEqual("1 >= 2", result.ToString());
            CheckIsBoolType(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void GeIntWrongArgType()
        {
            var builder = GetSimpleBuilder();
            var constant0 = builder.False;
            var constant1 = builder.True;
            builder.Ge(constant0, constant1);
        }

    }
}

