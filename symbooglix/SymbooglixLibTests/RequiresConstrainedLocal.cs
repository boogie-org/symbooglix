using NUnit.Framework;
using System;
using Microsoft.Boogie;
using symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class RequiresConstrainedLocal : SymbooglixTest, IBreakPointHandler
    {
        public RequiresConstrainedLocal()
        {
            setupDebug();
            setupCmdLineParser();
        }

        public Executor.HandlerAction handleBreakPoint(string name, Executor e)
        {
            // Find the "a" local variable
            var pair = e.currentState.getInScopeVariableAndExprByName("a");
            Variable V = pair.Key;
            Expr E = pair.Value;

            var FSV = new FindSymbolicsVisitor(e.currentState);
            FSV.Visit(E);
            Assert.IsTrue(FSV.symbolics.Count == 1);
            Assert.IsTrue(E is IdentifierExpr);
            var id = E as IdentifierExpr;

            // Check we have the expected constraint
            string expected = "bv8ugt(" + id.Name + ", 2bv8)";
            Assert.AreEqual(e.currentState.cm.constraints.Count, 1);
            Assert.IsTrue(e.currentState.cm.constraints[0].ToString() == expected);

            return Executor.HandlerAction.CONTINUE;

        }

        [Test()]
        public void NonRecursive()
        {
            p = loadProgram("programs/RequiresConstrainedLocal.bpl");
            e = getExecutor(p);
            e.registerBreakPointHandler(this);
            e.run(getMain(p));
        }
    }
}

