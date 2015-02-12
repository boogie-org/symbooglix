using System;
using NUnit.Framework;
using Microsoft.Boogie;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Havoc : SymbooglixTest
    {
        [Test()]
        public void simpleHavoc()
        {
            p = LoadProgramFrom(@"
                procedure main()
                {
                    var a:int;
                    a := 1;
                    assert {:symbooglix_bp ""a_is_concrete""} true;
                    havoc a;
                    assert {:symbooglix_bp ""a_is_symbolic""} true;
                }

                ", "test.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            int counter = 0;
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArgs)
            {
                switch (eventArgs.Name)
                {
                    case "a_is_concrete":
                        var aBefore = e.CurrentState.GetInScopeVariableAndExprByName("a");
                        var asLit = ExprUtil.AsLiteral(aBefore.Value);
                        Assert.IsNotNull(asLit);
                        Assert.IsTrue(asLit.isBigNum);
                        Assert.AreEqual(Microsoft.Basetypes.BigNum.FromInt(1), asLit.asBigNum);
                        break;
                    case "a_is_symbolic":
                        var aAfter = e.CurrentState.GetInScopeVariableAndExprByName("a");
                        Assert.AreNotSame(aBefore, aAfter);
                        var asId = ExprUtil.AsIdentifer(aAfter.Value);
                        Assert.IsNotNull(asId);
                        break;
                    default:
                        Assert.Fail("Unrecognised breakpoint");
                        break;
                }
                ++counter;
            };

            e.Run(GetMain(p));
            Assert.AreEqual(2, counter);
        }
    }
}

