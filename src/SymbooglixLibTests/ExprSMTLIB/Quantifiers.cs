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
    public class Quantifiers
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
                var printer = new SMTLIBQueryPrinter(writer, false, false);
                printer.PrintExpr(result);
                Assert.AreEqual("(forall (  (x Int) (y Int) ) (> (f x y  ) x ) )", writer.ToString());
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
                var printer = new SMTLIBQueryPrinter(writer, false, false);
                printer.PrintExpr(result);
                Assert.AreEqual("(exists (  (x Int) (y Int) ) (> (f x y  ) x ) )", writer.ToString());
            }
        }
    }
}

