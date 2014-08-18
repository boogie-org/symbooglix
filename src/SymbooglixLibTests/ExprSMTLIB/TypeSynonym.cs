using Microsoft.Boogie;
using NUnit.Framework;
using System;
using Symbooglix;
using System.IO;
using System.Collections.Generic;

namespace ExprSMTLIBTest
{
    [TestFixture()]
    public class TypeSynonym
    {
        private IExprBuilder builder;

        public TypeSynonym()
        {
            builder = new ExprBuilder();
        }

        [Test()]
        public void BitVector()
        {
            CheckType(BvType.GetBvType(2), builder.ConstantBV(3, 2), "(_ BitVec 2)","(= symbolic_0 (_ bv3 2) )");
        }

        [Test()]
        public void Integer()
        {
            CheckType(BasicType.Int, builder.ConstantInt(15), "Int", "(= symbolic_0 15 )");
        }

        [Test()]
        public void Boolean()
        {
            CheckType(BasicType.Bool, builder.ConstantBool(true), "Bool", "(= symbolic_0 true )");
        }

        [Test()]
        public void Real()
        {
            CheckType(BasicType.Real, builder.ConstantReal("0.5"), "Real", "(= symbolic_0 0.5 )");
        }

        private void CheckType(Microsoft.Boogie.Type type, LiteralExpr theConstant, string expectedType, string expectedExpr)
        {
            string result = null;
            using (var stringWriter = new StringWriter())
            {
                var printer = new SMTLIBQueryPrinter(stringWriter, false);

                // Make a typesynonym
                var typeDecl = new TypeSynonymDecl(Token.NoToken, "mysyn", null, type);
                var ts = new TypeSynonymAnnotation(Token.NoToken, typeDecl, new List<Microsoft.Boogie.Type>());

                // Check we get the basic type back
                Assert.AreEqual(expectedType, SMTLIBQueryPrinter.GetSMTLIBType(ts));

                // Now check it can be used in a query
                var typeIdent = new TypedIdent(Token.NoToken, "thetype", ts);
                var variable = new LocalVariable(Token.NoToken, typeIdent);
                var symbolic = new SymbolicVariable("symbolic_0", variable);
                var theExpr = Expr.Eq(symbolic.Expr, theConstant);

                printer.AddDeclarations(theExpr);
                printer.PrintExpr(theExpr);
                result = stringWriter.ToString();
            }

            Assert.AreEqual(expectedExpr, result);
        }
    }



}

