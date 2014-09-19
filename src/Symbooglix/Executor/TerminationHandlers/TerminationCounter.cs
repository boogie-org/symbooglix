using Microsoft.Boogie;
using System;
using System.Diagnostics;

namespace Symbooglix
{
    public class TerminationCounter : IExecutorEventHandler
    {
        // Counters
        public int Sucesses { get; private set;}
        public int FailingAsserts { get; private set;}
        public int UnsatisfiableRequiresOnEntry { get; private set;}
        public int FailingRequires { get; private set;}
        public int FailingEnsures { get; private set;}
        public int UnsatisfiableAssumes { get; private set;}
        public int UnsatisfiableEnsures { get; private set; }
        public int UnsatisfiableAxioms { get; private set;}
        public int DisallowedSpeculativePaths { get; private set; }

        public int NumberOfFailures
        {
            get
            {
                return FailingAsserts +
                UnsatisfiableRequiresOnEntry +
                FailingRequires +
                FailingEnsures +
                UnsatisfiableAssumes +
                UnsatisfiableEnsures +
                UnsatisfiableAxioms;
                // Note we don't consider a DisallowedSpeculativePath to be a failure
            }
        }

        public int NumberOfTerminatedStates
        {
            get { return NumberOfFailures + Sucesses + DisallowedSpeculativePaths; }
        }

        public TerminationCounter()
        {
            reset();
        }

        public void Connect(Executor e)
        {
            e.StateTerminated += this.handle;
        }

        public void Disconnect(Executor e)
        {
            e.StateTerminated -= this.handle;
        }

        private void handle(Object executor, Executor.ExecutionStateEventArgs arg)
        {
            var terminationType = arg.State.TerminationType;
            Debug.Assert(terminationType != null);

            if (terminationType is TerminatedWithoutError)
                Sucesses++;
            else if (terminationType is TerminatedAtUnsatisfiableEntryRequires)
                UnsatisfiableRequiresOnEntry++;
            else if (terminationType is TerminatedAtUnsatisfiableAssume)
                UnsatisfiableAssumes++;
            else if (terminationType is TerminatedAtFailingRequires)
                FailingRequires++;
            else if (terminationType is TerminatedAtFailingEnsures)
                FailingEnsures++;
            else if (terminationType is TerminatedAtFailingAssert)
                FailingAsserts++;
            else if (terminationType is TerminatedAtUnsatisfiableEnsures)
                UnsatisfiableEnsures++;
            else if (terminationType is TerminatedAtUnsatisfiableAxiom)
                UnsatisfiableAxioms++;
            else if (terminationType is TerminatedWithDisallowedSpeculativePath)
                DisallowedSpeculativePaths++;
            else
                throw new NotSupportedException("Can't handle Termination type " + terminationType.ToString());
        }

        public void reset()
        {
            Sucesses = 0;
            FailingAsserts = 0;
            UnsatisfiableRequiresOnEntry = 0;
            FailingRequires = 0;
            FailingEnsures = 0;
            UnsatisfiableAssumes = 0;
            UnsatisfiableEnsures = 0;
            DisallowedSpeculativePaths = 0;
        }

        public override string ToString()
        {
            return string.Format("[TerminationCounter:\n" +
                                 "  Sucesses={0}\n" +
                                 "  FailingAsserts={1},\n" +
                                 "  UnsatisfiableRequiresOnEntry={2}\n" +
                                 "  FailingRequires={3}\n" +
                                 "  FailingEnsures={4}\n" +
                                 "  UnsatisfiableAssumes={5}\n" +
                                 "  UnsatisfiableEnsures={6}\n" +
                                 "  UnsatisfiableAxioms={7}\n" +
                                 "  DisallowedSpeculativePath={8}\n" +
                                 "]",
                                 Sucesses,
                                 FailingAsserts,
                                 UnsatisfiableRequiresOnEntry,
                                 FailingRequires,
                                 FailingEnsures,
                                 UnsatisfiableAssumes,
                                 UnsatisfiableEnsures,
                                 UnsatisfiableAxioms,
                                 DisallowedSpeculativePaths);
        }

    }
}

