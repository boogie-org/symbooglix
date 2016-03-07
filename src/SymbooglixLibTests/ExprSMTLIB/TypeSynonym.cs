//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using Microsoft.Boogie;
using NUnit.Framework;
using System;
using Symbooglix;
using Symbooglix.Annotation;
using System.IO;
using System.Collections.Generic;

namespace ExprSMTLIBTest
{
    [TestFixture()]
    public class TypeSynonym : ExprSMTLIBTestBase
    {
        private IExprBuilder builder;

        public TypeSynonym()
        {
            builder = new SimpleExprBuilder(/*immutable=*/ true);
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

        [Test()]
        public void NestedInteger()
        {
            var ts1 = CreateTypeSynonym(BasicType.Int, "syn0");
            var ts2 = CreateTypeSynonym(ts1, "syn1");
            CheckType(ts2, builder.ConstantInt(15), "Int", "(= symbolic_0 15 )");
        }

        private Microsoft.Boogie.Type CreateTypeSynonym(Microsoft.Boogie.Type type, string name)
        {
            var typeDecl = new TypeSynonymDecl(Token.NoToken, name, null, type);
            var ts = new TypeSynonymAnnotation(Token.NoToken, typeDecl, new List<Microsoft.Boogie.Type>());
            return ts;
        }

        private void CheckType(Microsoft.Boogie.Type type, LiteralExpr theConstant, string expectedType, string expectedExpr)
        {
            string result = null;
            using (var stringWriter = new StringWriter())
            {
                var printer = GetPrinter(stringWriter);

                var ts = CreateTypeSynonym(type, "mysn");

                // Check we get the basic type back
                Assert.AreEqual(expectedType, SMTLIBQueryPrinter.GetSMTLIBType(ts));

                // Now check it can be used in a query
                var typeIdent = new TypedIdent(Token.NoToken, "thetype", ts);
                var variable = new LocalVariable(Token.NoToken, typeIdent);

                // SymbolicVariable constructor requires that a ProgramLocation is already attached
                variable.SetMetadata((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(variable));

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

