using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class UniqueVariables : SymbooglixTest
    {
        [Test()]
        public void ExhaustFiniteDomain()
        {
            p = LoadProgramFrom(@"
                const unique a:bool;
                const unique b:bool;
                const unique c:bool;

                procedure main()
                {
                    assume a || b || c;
                }
            ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            bool hit = false;
            e.StateTerminated += delegate(object sender, Executor.ExecutionStateEventArgs eventArgs)
            {
                Assert.IsInstanceOf<TerminatedAtUnsatisfiableAxiom>(eventArgs.State.TerminationType);
                var tt = eventArgs.State.TerminationType as TerminatedAtUnsatisfiableAxiom;
                // FIXME: GROSS! Boogie seems to rewrite the expression!
                Assert.AreEqual("(a <==> !b) && (a <==> !c) && (b <==> !c)", tt.ExitLocation.AsAxiom.Expr.ToString());
                hit = true;
            };

            bool exceptionRaised = false;

            try
            {
                e.Run(GetMain(p));
            }
            catch (InitialStateTerminated)
            {
                exceptionRaised = true;
            }
            Assert.IsTrue(hit);
            Assert.IsTrue(exceptionRaised);
        }

        [Test()]
        public void UniqueRestrictsValuesFailure()
        {
            p = LoadProgramFrom(@"
                const unique a:int;
                const unique b:int;
                const unique c:int;
                axiom a >= 0 && b >= 0 && c >= 0;

                procedure main()
                {
                    assert a <= 1 && b <= 1 && c <= 1;
                }
            ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var tc = new TerminationCounter();
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(1, tc.FailingAsserts);
            Assert.AreEqual(0, tc.Sucesses);
            Assert.AreEqual(1, tc.NumberOfTerminatedStates);
        }

        [Test()]
        public void UniqueRestrictsValuesFailureOrSuccess()
        {
            p = LoadProgramFrom(@"
                const unique a:int;
                const unique b:int;
                const c:int;
                axiom a >= 0 && b >= 0 && c >= 0;

                procedure main()
                {
                    assert a <= 1 && b <= 1 && c <= 1;
                }
            ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var tc = new TerminationCounter();
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(1, tc.FailingAsserts);
            Assert.AreEqual(1, tc.Sucesses);
            Assert.AreEqual(2, tc.NumberOfTerminatedStates);
        }

        [Test()]
        public void BoolsDomainAssertAorB()
        {
            p = LoadProgramFrom(@"
                const unique a:bool;
                const unique b:bool;

                procedure main()
                {
                    assert a || b;
                }
            ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var tc = new TerminationCounter();
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(1, tc.Sucesses);
            Assert.AreEqual(1, tc.NumberOfTerminatedStates);
        }

        [Test()]
        public void BoolsDomainAssertAandB()
        {
            p = LoadProgramFrom(@"
                const unique a:bool;
                const unique b:bool;

                procedure main()
                {
                    assert a && b;
                }
            ", "test.bpl");

            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var tc = new TerminationCounter();
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(0, tc.Sucesses);
            Assert.AreEqual(1, tc.FailingAsserts);
            Assert.AreEqual(1, tc.NumberOfTerminatedStates);
        }
    }
}

