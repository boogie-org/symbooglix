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
using System.Collections.Generic;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests
{
    public class UninterpretedFunctionsSimpleBuilder
    {
        public UninterpretedFunctionsSimpleBuilder()
        {
            // This is a hack
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();
        }

        private FunctionCallBuilder GetFCBuilder()
        {
            return new FunctionCallBuilder();
        }

        private IExprBuilder GetSEBuilder()
        {
            return new SimpleExprBuilder(/*immutable=*/ true);
        }

        [Test()]
        public void CreateFunctionCall()
        {
            var FCB = GetFCBuilder();
            var fc0 = FCB.CreateCachedUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
                {
                    BasicType.GetBvType(2),
                    BasicType.GetBvType(2)
                 });
            // SimpleExpr builder should hit its cache if we ask for foo again
            var fc1 = FCB.CreateCachedUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });

            Assert.AreSame(fc0, fc1);
        }

        [Test()]
        public void CreateFunctionCallDistinct()
        {
            var FCB = GetFCBuilder();
            var fc0 = FCB.CreateCachedUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
            // SimpleExpr builder should not hit the cache here as we ask for different function name
            var fc1 = FCB.CreateCachedUninterpretedFunctionCall("foo2",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });

            Assert.AreNotSame(fc0, fc1);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void CreateFunctionCallMistmatchReturnType()
        {
            var FCB = GetFCBuilder();
            FCB.CreateCachedUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
            // SimpleExpr builder should hit its cache if we ask for foo again. We ask for the wrong type here
            FCB.CreateCachedUninterpretedFunctionCall("foo",
                BasicType.Int,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void CreateFunctionCallMistmatchWrongNumberOfArgs()
        {
            var FCB = GetFCBuilder();
            FCB.CreateCachedUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
            // SimpleExpr builder should hit its cache if we ask for foo again. We ask for the wrong number of args here
            FCB.CreateCachedUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2)
            });
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void CreateFunctionCallMistmatchArgType()
        {
            var FCB = GetFCBuilder();
            FCB.CreateCachedUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
            // SimpleExpr builder should hit its cache if we ask for foo again. We ask for the wrong type here
            FCB.CreateCachedUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2),
                BasicType.Bool
            });
        }

        [Test()]
        public void CreateFunctionCallExpr()
        {
            var FCB = GetFCBuilder();
            var SEB = GetSEBuilder();
            var fc = FCB.CreateCachedUninterpretedFunctionCall("foo",
                          BasicType.Bool,
                          new List<Microsoft.Boogie.Type>() {
                    BasicType.GetBvType(2),
                    BasicType.GetBvType(2)
                });
            var call = SEB.UFC(fc, SEB.ConstantBV(0, 2), SEB.ConstantBV(1, 2));
            Assert.AreEqual("foo(0bv2, 1bv2)", call.ToString());
            Assert.AreEqual(BasicType.Bool, call.ShallowType);
            Assert.IsNotNull(call.Type);
            Assert.AreEqual(BasicType.Bool, call.Type);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void CreateFunctionCallExprWrongArgTypes()
        {
            var FCB = GetFCBuilder();
            var SEB = GetSEBuilder();
            var fc = FCB.CreateCachedUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>() {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
            SEB.UFC(fc, SEB.ConstantBV(0, 3), SEB.ConstantBV(1, 3));
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void CreateFunctionCallExprWrongArgCount()
        {
            var FCB = GetFCBuilder();
            var SEB = GetSEBuilder();
            var fc = FCB.CreateCachedUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>() {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
            SEB.UFC(fc, SEB.ConstantBV(0, 3));
        }
    }
}

