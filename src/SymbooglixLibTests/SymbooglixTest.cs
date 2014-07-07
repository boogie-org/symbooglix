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

        public static void setupDebug()
        {
            // Debug log output goes to standard error.
            // Failing System.Diagnostics failures trigger NUnit assertion failures
            Debug.Listeners.Add(new AssertionTextWriterTraceListener(Console.Error));
        }

        public static void setupCmdLineParser()
        {
            // THIS IS A HACK. Boogie's methods
            // depend on its command line parser being set!
            CommandLineOptions.Install(new Microsoft.Boogie.CommandLineOptions());
        }

        public static Program loadProgram(String path)
        {
            setupDebug();
            Assert.IsTrue(File.Exists(path));

            setupCmdLineParser();

            int errors = 0;
            Program p = null;
            List<String> defines = null;
            errors = Parser.Parse(path, defines, out p);
            Assert.AreEqual(0, errors);
            Assert.IsNotNull(p);

            // Resolve
            errors = p.Resolve();
            Assert.AreEqual(0, errors);

            // Type check
            errors = p.Typecheck();
            Assert.AreEqual(0, errors);

            return p;
        }

        public static Executor getExecutor(Program p, IStateScheduler scheduler = null, ISolver solver = null)
        {
            if (scheduler == null )
                scheduler = new DFSStateScheduler();

            if (solver == null)
                solver = new DummySolver();

            Executor e = new Executor(p, scheduler, solver);

            IExecutorHandler verifier = new VerifyUnmodifiedProcedureHandler();
            e.registerPreEventHandler(verifier);
            e.registerPostEventHandler(verifier);
            return e;
        }

        public static Implementation getMain(Program p)
        {
            var imp = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First();
            Assert.AreNotEqual(null, imp);
            return imp;
        }

        public static BvConst getBVFromLiteral(Expr l)
        {
            Assert.IsTrue(l is LiteralExpr);
            LiteralExpr litExpr = l as LiteralExpr;
            Assert.IsTrue(litExpr.isBvConst);
            BvConst literalBV = litExpr.asBvConst;
            return literalBV;
        }

        public static IdentifierExpr CheckIsSymbolicIdentifier(Expr e, ExecutionState state)
        {
            Assert.IsInstanceOfType(typeof(IdentifierExpr), e);
            IdentifierExpr sym = e as IdentifierExpr;
            Assert.IsTrue(state.Symbolics.Where(s => s.Expr == sym).Count() > 0);
            return sym;
        }

        public static LiteralExpr CheckIsLiteralBVConstWithValue(Expr e, BigNum value)
        {
            Assert.IsInstanceOfType(typeof(LiteralExpr), e);
            LiteralExpr lit = e as LiteralExpr;
            Assert.IsTrue(lit.isBvConst);
            BvConst litBV = lit.asBvConst;
            Assert.AreEqual(value, litBV.Value);
            return lit;
        }
    }
}

