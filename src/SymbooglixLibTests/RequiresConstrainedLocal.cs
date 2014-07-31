using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class RequiresConstrainedLocal : SymbooglixTest
    {
        public RequiresConstrainedLocal()
        {
            setupDebug();
            setupCmdLineParser();
        }

        [Test()]
        public void NonRecursive()
        {
            p = loadProgram("programs/RequiresConstrainedLocal.bpl");
            e = getExecutor(p);
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                // Find the "a" local variable
                var pair = e.CurrentState.GetInScopeVariableAndExprByName("a");
                Variable V = pair.Key;
                Expr E = pair.Value;

                Assert.IsTrue(E is IdentifierExpr);
                var id = E as IdentifierExpr;
                Assert.IsTrue(id.Decl is SymbolicVariable);

                // Check we have the expected constraint
                string expected = "bv8ugt(" + id.Name + ", 2bv8)";
                Assert.AreEqual(e.CurrentState.Constraints.Constraints.Count, 1);
                Assert.IsTrue(e.CurrentState.Constraints.Constraints[0].ToString() == expected);
            };
            e.Run(getMain(p));
        }
    }
}

