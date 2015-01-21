using NUnit.Framework;
using System;
using System.Collections.Generic;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests
{
    public class UninterpretedFunctions
    {
        public UninterpretedFunctions ()
        {
            // This is a hack
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();
        }

        private IExprBuilder GetBuilder()
        {
            return new SimpleExprBuilder();
        }

        [Test()]
        public void CreateFunctionCall()
        {
            var builder = GetBuilder();
            var fc0 = builder.CreateUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
                {
                    BasicType.GetBvType(2),
                    BasicType.GetBvType(2)
                 });
            // SimpleExpr builder should hit its cache if we ask for foo again
            var fc1 = builder.CreateUninterpretedFunctionCall("foo",
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
            var builder = GetBuilder();
            var fc0 = builder.CreateUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
            // SimpleExpr builder should not hit the cache here as we ask for different function name
            var fc1 = builder.CreateUninterpretedFunctionCall("foo2",
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
            var builder = GetBuilder();
            builder.CreateUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
            // SimpleExpr builder should hit its cache if we ask for foo again. We ask for the wrong type here
            builder.CreateUninterpretedFunctionCall("foo",
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
            var builder = GetBuilder();
            builder.CreateUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
            // SimpleExpr builder should hit its cache if we ask for foo again. We ask for the wrong number of args here
            builder.CreateUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2)
            });
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void CreateFunctionCallMistmatchArgType()
        {
            var builder = GetBuilder();
            builder.CreateUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>()
            {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
            // SimpleExpr builder should hit its cache if we ask for foo again. We ask for the wrong type here
            builder.CreateUninterpretedFunctionCall("foo",
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
            var builder = GetBuilder();
            var fc = builder.CreateUninterpretedFunctionCall("foo",
                          BasicType.Bool,
                          new List<Microsoft.Boogie.Type>() {
                    BasicType.GetBvType(2),
                    BasicType.GetBvType(2)
                });
            var call = builder.UFC(fc, builder.ConstantBV(0, 2), builder.ConstantBV(1, 2));
            Assert.AreEqual("foo(0bv2, 1bv2)", call.ToString());
            Assert.AreEqual(BasicType.Bool, call.ShallowType);
            Assert.IsNotNull(call.Type);
            Assert.AreEqual(BasicType.Bool, call.Type);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void CreateFunctionCallExprWrongArgTypes()
        {
            var builder = GetBuilder();
            var fc = builder.CreateUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>() {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
            builder.UFC(fc, builder.ConstantBV(0, 3), builder.ConstantBV(1, 3));
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void CreateFunctionCallExprWrongArgCount()
        {
            var builder = GetBuilder();
            var fc = builder.CreateUninterpretedFunctionCall("foo",
                BasicType.Bool,
                new List<Microsoft.Boogie.Type>() {
                BasicType.GetBvType(2),
                BasicType.GetBvType(2)
            });
            builder.UFC(fc, builder.ConstantBV(0, 3));
        }
    }
}

