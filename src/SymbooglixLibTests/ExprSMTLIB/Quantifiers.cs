using System;
using System.Collections.Generic;
using System.IO;
using NUnit.Framework;
using Microsoft.Boogie;
using Symbooglix;

using BPLType = Microsoft.Boogie.Type;

namespace ExprSMTLIBTest
{
    [TestFixture()]
    public class Quantifiers : ExprSMTLIBTestBase
    {

        // FIXME: Taken from SimpleExprBuilderTestBase. This needs to be refactored
        protected Tuple<Variable, IdentifierExpr> GetVarAndIdExpr(string name, Microsoft.Boogie.Type type, bool isBound=false)
        {
            var typeIdent = new TypedIdent(Token.NoToken, name, type);

            Variable v = null;
            if (isBound)
            {
                v = new BoundVariable(Token.NoToken, typeIdent);
            }
            else
            {
                v = new GlobalVariable(Token.NoToken, typeIdent);
            }

            var id = new IdentifierExpr(Token.NoToken, v, /*immutable=*/ true);
            return new Tuple<Variable, IdentifierExpr>(v, id);
        }

        private IExprBuilder MkBuilder()
        {
            return new SimpleExprBuilder(/*immutable=*/true);
        }

        private delegate Trigger SetupTriggersDeligate(IExprBuilder builder, FunctionCall f, IdentifierExpr xId, IdentifierExpr yId);

        private Expr buildQuant(bool isForAll, SetupTriggersDeligate sutd)
        {
            var builder = MkBuilder();
            Assert.IsNotNull(builder);
            var xPair = GetVarAndIdExpr("x", BasicType.Int, /*isBound=*/true);
            var xVar = xPair.Item1;
            var xId = xPair.Item2;
            var yPair = GetVarAndIdExpr("y", BasicType.Int, /*isBound=*/ true);
            var yId = yPair.Item2;
            var yVar = yPair.Item1;

            var fcb = new FunctionCallBuilder();
            var funcCall = fcb.CreateCachedUninterpretedFunctionCall("f",
                BPLType.Int,
                new List<BPLType>() { BPLType.Int, BPLType.Int });

            // get triggers
            var triggers = sutd(builder, funcCall, xId, yId);

            var body = builder.Gt(builder.UFC(funcCall, xId, yId), xId);

            Expr result = null;
            if (isForAll)
                result = builder.ForAll(new List<Variable>() { xVar, yVar }, body, triggers);
            else
                result = builder.Exists(new List<Variable>() { xVar, yVar }, body, triggers);

            return result;
        }

        [Test()]
        public void ForAllNoTriggers()
        {
            Expr result = buildQuant(/*isForAll=*/true,
                delegate(IExprBuilder builder, FunctionCall f, IdentifierExpr xId, IdentifierExpr yId)
            {
                return null;
            });
            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.PrintExpr(result);
                Assert.AreEqual("(forall (  (x Int) (y Int) ) (> (f x y  ) x ) )", writer.ToString());
            }
        }

        [Test()]
        public void ForAllSinglePositiveTrigger()
        {
            Expr result = buildQuant(/*isForAll=*/true,
                delegate(IExprBuilder builder, FunctionCall f, IdentifierExpr xId, IdentifierExpr yId)
            {
                var triggerExpr = builder.UFC(f, xId, yId);
                var trigger = new Trigger(Token.NoToken, /*pos=*/true, new List<Expr>() {triggerExpr},null);
                return trigger;
            });
            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.PrintExpr(result);
                Assert.AreEqual("(forall (  (x Int) (y Int) ) (! (> (f x y  ) x ) :pattern ( (f x y  ) ) ) )", writer.ToString());
            }
        }

        [Test()]
        public void ForAllTwoPositiveTriggers()
        {
            Expr result = buildQuant(/*isForAll=*/true,
                delegate(IExprBuilder builder, FunctionCall f, IdentifierExpr xId, IdentifierExpr yId)
            {
                var triggerExpr = builder.UFC(f, xId, yId);
                var trigger = new Trigger(Token.NoToken, /*pos=*/true, new List<Expr>() {triggerExpr},null);
                var triggerExpr2 = builder.UFC(f, yId, xId);
                var trigger2 = new Trigger(Token.NoToken, /*pos=*/true, new List<Expr>() {triggerExpr2}, trigger);
                return trigger2;
            });
            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.PrintExpr(result);
                Assert.AreEqual("(forall (  (x Int) (y Int) ) (! (> (f x y  ) x ) :pattern ( (f y x  ) ):pattern ( (f x y  ) ) ) )", writer.ToString());
            }
        }

        [Test()]
        public void ForAllSingleTriggerObjMultipleExpr()
        {
            Expr result = buildQuant(/*isForAll=*/true,
                delegate(IExprBuilder builder, FunctionCall f, IdentifierExpr xId, IdentifierExpr yId)
            {
                var triggerExpr = builder.UFC(f, xId, yId);
                var triggerExpr2 = builder.UFC(f, yId, xId);
                var trigger = new Trigger(Token.NoToken, /*pos=*/true, new List<Expr>() {triggerExpr, triggerExpr2},null);
                return trigger;
            });
            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.PrintExpr(result);
                Assert.AreEqual("(forall (  (x Int) (y Int) ) (! (> (f x y  ) x ) :pattern ( (f x y  ) (f y x  ) ) ) )", writer.ToString());
            }
        }

        [Test()]
        public void ForAllSingleNegativeTrigger()
        {
            Expr result = buildQuant(/*isForAll=*/true,
                delegate(IExprBuilder builder, FunctionCall f, IdentifierExpr xId, IdentifierExpr yId)
            {
                var triggerExpr = builder.UFC(f, xId, yId);
                var trigger = new Trigger(Token.NoToken, /*pos=*/false, new List<Expr>() {triggerExpr},null);
                return trigger;
            });
            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.PrintExpr(result);
                Assert.AreEqual("(forall (  (x Int) (y Int) ) (! (> (f x y  ) x ) :no-pattern (f x y  ) ) )", writer.ToString());
            }
        }


        [Test()]
        public void ExistsNoTriggers()
        {
            Expr result = buildQuant(/*isForAll=*/false,
                delegate(IExprBuilder builder, FunctionCall f, IdentifierExpr xId, IdentifierExpr yId)
            {
                return null;
            });
            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.PrintExpr(result);
                Assert.AreEqual("(exists (  (x Int) (y Int) ) (> (f x y  ) x ) )", writer.ToString());
            }
        }

        [Test()]
        public void ExistsSinglePositiveTrigger()
        {
            Expr result = buildQuant(/*isForAll=*/false,
                delegate(IExprBuilder builder, FunctionCall f, IdentifierExpr xId, IdentifierExpr yId)
            {
                var triggerExpr = builder.UFC(f, xId, yId);
                var trigger = new Trigger(Token.NoToken, /*pos=*/true, new List<Expr>() {triggerExpr},null);
                return trigger;
            });
            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.PrintExpr(result);
                Assert.AreEqual("(exists (  (x Int) (y Int) ) (! (> (f x y  ) x ) :pattern ( (f x y  ) ) ) )", writer.ToString());
            }
        }

        [Test()]
        public void ExistsTwoPositiveTriggers()
        {
            Expr result = buildQuant(/*isForAll=*/false,
                delegate(IExprBuilder builder, FunctionCall f, IdentifierExpr xId, IdentifierExpr yId)
            {
                var triggerExpr = builder.UFC(f, xId, yId);
                var trigger = new Trigger(Token.NoToken, /*pos=*/true, new List<Expr>() {triggerExpr},null);
                var triggerExpr2 = builder.UFC(f, yId, xId);
                var trigger2 = new Trigger(Token.NoToken, /*pos=*/true, new List<Expr>() {triggerExpr2}, trigger);
                return trigger2;
            });
            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.PrintExpr(result);
                Assert.AreEqual("(exists (  (x Int) (y Int) ) (! (> (f x y  ) x ) :pattern ( (f y x  ) ):pattern ( (f x y  ) ) ) )", writer.ToString());
            }
        }

        [Test()]
        public void ExistsSingleTriggerObjMultipleExpr()
        {
            Expr result = buildQuant(/*isForAll=*/false,
                delegate(IExprBuilder builder, FunctionCall f, IdentifierExpr xId, IdentifierExpr yId)
            {
                var triggerExpr = builder.UFC(f, xId, yId);
                var triggerExpr2 = builder.UFC(f, yId, xId);
                var trigger = new Trigger(Token.NoToken, /*pos=*/true, new List<Expr>() {triggerExpr, triggerExpr2},null);
                return trigger;
            });
            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.PrintExpr(result);
                Assert.AreEqual("(exists (  (x Int) (y Int) ) (! (> (f x y  ) x ) :pattern ( (f x y  ) (f y x  ) ) ) )", writer.ToString());
            }
        }

        [Test()]
        public void ExistsSingleNegativeTrigger()
        {
            Expr result = buildQuant(/*isForAll=*/false,
                delegate(IExprBuilder builder, FunctionCall f, IdentifierExpr xId, IdentifierExpr yId)
            {
                var triggerExpr = builder.UFC(f, xId, yId);
                var trigger = new Trigger(Token.NoToken, /*pos=*/false, new List<Expr>() {triggerExpr},null);
                return trigger;
            });
            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.PrintExpr(result);
                Assert.AreEqual("(exists (  (x Int) (y Int) ) (! (> (f x y  ) x ) :no-pattern (f x y  ) ) )", writer.ToString());
            }
        }
    }
}

