﻿using Microsoft.Boogie;
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
    }
}

