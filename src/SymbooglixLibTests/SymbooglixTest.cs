//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using Symbooglix;
using Symbooglix.Solver;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using Microsoft.Basetypes;
using Microsoft.Boogie;
using NUnit.Framework;

namespace SymbooglixLibTests
{
    public abstract class SymbooglixTest
    {
        protected Program p;
        protected Executor e;

        public static string TrimNewLines(string original)
        {
            return original.TrimEnd(new char[] { '\n', '\r' });
        }

        public static void SetupDebug()
        {
            // Debug log output goes to standard error.
            // Failing System.Diagnostics failures trigger NUnit assertion failures
            Debug.Listeners.Add(new AssertionTextWriterTraceListener(Console.Error));
        }

        public static void SetupCmdLineParser()
        {
            // THIS IS A HACK. Boogie's methods
            // depend on its command line parser being set!
            CommandLineOptions.Install(new Microsoft.Boogie.CommandLineOptions());
        }

        public static Program LoadProgramFrom(String path)
        {
            SetupDebug();
            SetupCmdLineParser();
            Assert.IsNotNullOrEmpty(path);
            Assert.IsTrue(File.Exists(path));

            int errors = 0;
            Program p = null;
            List<String> defines = null;
            errors = Parser.Parse(path, defines, out p);
            Assert.AreEqual(0, errors);
            Assert.IsNotNull(p);

            return ResolveAndTypeCheck(p);
        }

        private static Program ResolveAndTypeCheck(Program p)
        {
            int errors = 0;
            // Resolve
            errors = p.Resolve();
            Assert.AreEqual(0, errors);

            // Type check
            errors = p.Typecheck();
            Assert.AreEqual(0, errors);

            return p;
        }

        public static Program LoadProgramFrom(string text, string fileName)
        {
            SetupDebug();
            SetupCmdLineParser();
            Assert.IsNotNullOrEmpty(text);
            Assert.IsNotNullOrEmpty(fileName);

            int errors = 0;
            Program program = null;
            errors = Parser.Parse(text, fileName, out program);
            Assert.AreEqual(0, errors);
            Assert.IsNotNull(program);

            return ResolveAndTypeCheck(program);
        }

        public static ISolver GetSolver()
        {
            // FIXME: Allow control over which solver is used

            // FIXME: Relative paths are fragile!
            // Look in the directory of the symbooglix binaries for solver
            var pathToSolver = "../../../Symbooglix/bin/{0}/z3".Replace('/', Path.DirectorySeparatorChar);

            // Depending on the build type choose which directory we search for the Solver
            #if DEBUG
            pathToSolver = String.Format(pathToSolver, "Debug");
            #else
            pathToSolver = String.Format(pathToSolver, "Release");
            #endif

            if (!File.Exists(pathToSolver))
            {
                pathToSolver += ".exe";
            }

            if (!File.Exists(pathToSolver))
                Assert.Fail("Could not find solver at \"{0}\"", pathToSolver);

            var solver = new SimpleSolver(new Z3SMTLIBSolver(/*useNamedAttributes=*/ true, pathToSolver, /*persistentProcess=*/ true, true));
            solver.SetTimeout(10);
            return solver;

        }

        public static Executor GetExecutor(Program p, IStateScheduler scheduler = null, ISolver solver = null, bool useConstantFolding=false)
        {
            if (scheduler == null )
                scheduler = new DFSStateScheduler();

            if (solver == null)
                solver = new SimpleSolver(new DummySolver());

            IExprBuilder builder = new SimpleExprBuilder(/*immutable=*/ true);

            if (useConstantFolding)
            {
                builder = new ConstantFoldingExprBuilder(new ConstantCachingExprBuilder(builder));
            }

            Executor e = new Executor(p, scheduler, solver, builder, new SimpleSymbolicPool());

            return e;
        }

        public static Implementation GetMain(Program p)
        {
            var imp = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First();
            Assert.AreNotEqual(null, imp);
            return imp;
        }

        public static BvConst GetBVFromLiteral(Expr l)
        {
            Assert.IsTrue(l is LiteralExpr);
            LiteralExpr litExpr = l as LiteralExpr;
            Assert.IsTrue(litExpr.isBvConst);
            BvConst literalBV = litExpr.asBvConst;
            return literalBV;
        }

        public static IdentifierExpr CheckIsSymbolicIdentifier(Expr e, ExecutionState state)
        {
            var asSym = ExprUtil.AsSymbolicVariable(e);
            Assert.IsNotNull(asSym);

            // FIXME: Find a convenient way to test this
            // Check the state is aware of it too
            // Assert.IsTrue(state.Symbolics.Where(s => s.Expr == identiferForSymbolic).Count() > 0);
           
            return asSym.Expr;
        }

        public static LiteralExpr CheckIsLiteralBVConstWithValue(Expr e, BigNum value)
        {
            Assert.IsInstanceOf<LiteralExpr>(e);
            LiteralExpr lit = e as LiteralExpr;
            Assert.IsTrue(lit.isBvConst);
            BvConst litBV = lit.asBvConst;
            Assert.AreEqual(value, litBV.Value);
            return lit;
        }
    }
}

