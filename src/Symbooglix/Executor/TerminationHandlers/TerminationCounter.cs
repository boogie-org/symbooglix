using Microsoft.Boogie;
using System;

namespace Symbooglix
{
    public class TerminationCounter : ITerminationHandler
    {
        // Counters
        public int Sucesses { get; private set;}
        public int FailingAsserts { get; private set;}
        public int UnsatisfiableRequires { get; private set;}
        public int FailingEnsures { get; private set;}
        public int UnsatisfiableAssumes { get; private set;}

        public int NumberOfFailures
        {
            get { return FailingAsserts + UnsatisfiableRequires + FailingEnsures + UnsatisfiableAssumes; }
        }

        public int NumberOfTerminatedStates
        {
            get { return NumberOfFailures + Sucesses; }
        }

        public TerminationCounter()
        {
            reset();
        }

        public void reset()
        {
            Sucesses = 0;
            FailingAsserts = 0;
            UnsatisfiableRequires = 0;
            FailingEnsures = 0;
            UnsatisfiableAssumes = 0;
        }

        public void handleSuccess(ExecutionState s)
        {
            ++Sucesses;
        }

        public void handleFailingAssert(ExecutionState s)
        {
            ++FailingAsserts;
        }

        public void handleUnsatisfiableRequires(ExecutionState s, Requires requiresStatement)
        {
            ++UnsatisfiableRequires;
        }

        public void handleFailingEnsures(ExecutionState s, Ensures ensuresStatement)
        {
            ++FailingEnsures;
        }

        public void handleUnsatisfiableAssume(ExecutionState s)
        {
            ++UnsatisfiableAssumes;
        }
            

        public override string ToString()
        {
            return string.Format("[TerminationCounter:\n" +
                                 "  Sucesses={0}\n" +
                                 "  FailingAsserts={1},\n" +
                                 "  UnsatisfiableRequires={2}\n" +
                                 "  FailingEnsures={3}\n" +
                                 "  UnsatisfiableAssumes={4}\n" +
                                 "]", Sucesses, FailingAsserts, UnsatisfiableRequires, FailingEnsures, UnsatisfiableAssumes);
        }

    }
}

