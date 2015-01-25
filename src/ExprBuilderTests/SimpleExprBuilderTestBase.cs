using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests
{
    public class SimpleExprBuilderTestBase : IErrorSink
    {
        public SimpleExprBuilderTestBase()
        {
            // This is a hack
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();
        }

        public IExprBuilder GetBuilder()
        {
            return new SimpleExprBuilder();
        }

        public void Error(IToken tok, string msg)
        {
            Assert.Fail(msg);
        }

        protected void CheckBvBuiltIn(Expr e, string expected)
        {
            Assert.IsInstanceOf<NAryExpr>(e);
            var asNary = e as NAryExpr;
            Assert.IsInstanceOf<FunctionCall>(asNary.Fun);
            var fc = asNary.Fun as FunctionCall;
            var actual = QKeyValue.FindStringAttribute(fc.Func.Attributes, "bvbuiltin");
            Assert.IsNotNullOrEmpty(actual);
            Assert.AreEqual(expected, actual);
        }

        protected void CheckIsBoolType(Expr result)
        {
            var shallowType = result.ShallowType;
            Assert.IsNotNull(shallowType);
            Assert.IsTrue(shallowType.IsBool);
            var t = result.Type;
            Assert.IsNotNull(t);
            Assert.IsTrue(t.IsBool);
            var TC = new TypecheckingContext(this);
            result.Typecheck(TC);
        }

        protected void CheckIsBvType(Expr result, int width)
        {
            var shallowType = result.ShallowType;
            Assert.IsNotNull(shallowType);
            Assert.IsTrue(shallowType.IsBv);
            Assert.AreEqual(width, shallowType.BvBits);
            var t = result.Type;
            Assert.IsNotNull(t);
            Assert.IsTrue(t.IsBv);
            Assert.AreEqual(width, t.BvBits);
            var TC = new TypecheckingContext(this);
            result.Typecheck(TC);
        }

        protected void CheckIsReal(Expr result)
        {
            Assert.IsTrue(result.ShallowType.IsReal);
            Assert.IsNotNull(result.Type);
            Assert.IsTrue(result.Type.IsReal);
            var TC = new TypecheckingContext(this);
            result.Typecheck(TC);
        }

        protected void CheckIsInt(Expr result)
        {
            Assert.IsTrue(result.ShallowType.IsInt);
            Assert.IsNotNull(result.Type);
            Assert.IsTrue(result.Type.IsInt);
            var TC = new TypecheckingContext(this);
            result.Typecheck(TC);
        }

        protected void CheckType(Expr e, Predicate<Microsoft.Boogie.Type> p)
        {
            Assert.IsNotNull(e.ShallowType);
            Assert.IsTrue(p(e.ShallowType));
            Assert.IsNotNull(e.Type);
            Assert.AreEqual(e.ShallowType, e.Type);
            var TC = new TypecheckingContext(this);
            e.Typecheck(TC);
        }
    }
}

