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
using Symbooglix;
using Symbooglix.Annotation;
using System;
using System.Collections.Generic;
using System.IO;


namespace ExprSMTLIBTest
{
    [TestFixture()]
    public class TypeConstructor : ExprSMTLIBTestBase
    {
        [Test()]
        public void NoArguments()
        {
            var tcDecl = new TypeCtorDecl(Token.NoToken, "fox", 0);
            var tc = new CtorType(Token.NoToken, tcDecl, new List <Microsoft.Boogie.Type>());
            var tcTypeIdent = new TypedIdent(Token.NoToken, "fox", tc);
            var gv = new GlobalVariable(Token.NoToken, tcTypeIdent);

            // FIXME: The Symbolic constructor shouldn't really need the program location
            gv.SetMetadata<ProgramLocation>((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(gv));
            var sym = new SymbolicVariable("y", gv);

            var builder = new SimpleExprBuilder(/*immutable=*/ true);
            var eq = builder.Eq(sym.Expr, sym.Expr);
            Assert.IsNotInstanceOf<LiteralExpr>(eq); // Check that it wasn't constant folded

            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.AddDeclarations(eq);
                printer.PrintSortDeclarations();
                Assert.AreEqual("(declare-sort @fox)", writer.ToString().Trim());
            }
        }

        [Test ()]
        public void MapWithTypeConstructorTypesNoArguments()
        {
            var tcDecl = new TypeCtorDecl(Token.NoToken, "fox", 0);
            var tc = new CtorType(Token.NoToken, tcDecl, new List<Microsoft.Boogie.Type>());
            var tcDecl2 = new TypeCtorDecl(Token.NoToken, "fox_two", 0);
            var tc2 = new CtorType(Token.NoToken, tcDecl2, new List<Microsoft.Boogie.Type>());
            var tcDecl3 = new TypeCtorDecl(Token.NoToken, "fox_three", 0);
            var tc3 = new CtorType(Token.NoToken, tcDecl3, new List<Microsoft.Boogie.Type>());
            var mapType = new MapType(
                Token.NoToken,
                new List<Microsoft.Boogie.TypeVariable>(),
                new List<Microsoft.Boogie.Type>() { tc, tc2 },
                tc3);
            var mapTypeTypeIdent = new TypedIdent(Token.NoToken, "mapx", mapType);
            var gv = new GlobalVariable(Token.NoToken, mapTypeTypeIdent);

            // FIXME: The Symbolic constructor shouldn't really need the program location
            gv.SetMetadata<ProgramLocation>((int)AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(gv));
            var sym = new SymbolicVariable("y", gv);

            var builder = new SimpleExprBuilder(/*immutable=*/ true);
            var eq = builder.Eq(sym.Expr, sym.Expr);
            Assert.IsNotInstanceOf<LiteralExpr>(eq); // Check that it wasn't constant folded

            using (var writer = new StringWriter()) {
                var printer = GetPrinter(writer);
                printer.AddDeclarations(eq);
                printer.PrintSortDeclarations();
                var str = writer.ToString().Trim();
                // Check we can see all the sort declarations we expect but don't depend on their order
                Assert.IsTrue(str.Contains("(declare-sort @fox)"));
                Assert.IsTrue(str.Contains("(declare-sort @fox_two)"));
                Assert.IsTrue(str.Contains("(declare-sort @fox_three)"));
            }
        }


        [Test(),ExpectedException(typeof(NotSupportedException))]
        public void Arguments()
        {
            var tcDecl = new TypeCtorDecl(Token.NoToken, "fox", 1);
            var tc = new CtorType(Token.NoToken, tcDecl, new List <Microsoft.Boogie.Type>() { Microsoft.Boogie.Type.Bool});
            var tcTypeIdent = new TypedIdent(Token.NoToken, "fox", tc);
            var gv = new GlobalVariable(Token.NoToken, tcTypeIdent);

            // FIXME: The Symbolic constructor shouldn't really need the program location
            gv.SetMetadata<ProgramLocation>((int) AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(gv));
            var sym = new SymbolicVariable("y", gv);

            var builder = new SimpleExprBuilder(/*immutable=*/ true);
            var eq = builder.Eq(sym.Expr, sym.Expr);
            Assert.IsNotInstanceOf<LiteralExpr>(eq); // Check that it wasn't constant folded

            using (var writer = new StringWriter())
            {
                var printer = GetPrinter(writer);
                printer.AddDeclarations(eq);
                printer.PrintSortDeclarations();
                Assert.AreEqual("(declare-sort @fox)\n", writer.ToString());
            }
        }
    }
}

