using Microsoft.Boogie;
using System;
using System.Diagnostics;
using System.Collections.Generic;

namespace Symbooglix
{
    public class TerminationCounter : IExecutorEventHandler
    {
        // Counters
        public int Sucesses { get { return GetCounter<TerminatedWithoutError>(); }}
        public int FailingAsserts { get { return GetCounter<TerminatedAtFailingAssert>(); }}
        public int UnsatisfiableRequiresOnEntry { get { return GetCounter<TerminatedAtUnsatisfiableEntryRequires>(); }}
        public int FailingRequires { get { return GetCounter<TerminatedAtFailingRequires>(); }}
        public int FailingEnsures { get { return GetCounter<TerminatedAtFailingEnsures>(); }}
        public int UnsatisfiableAssumes { get { return GetCounter<TerminatedAtUnsatisfiableAssume>(); }}
        public int UnsatisfiableEnsures { get { return GetCounter<TerminatedAtUnsatisfiableEnsures>(); } }
        public int UnsatisfiableAxioms { get { return GetCounter<TerminatedAtUnsatisfiableAxiom>(); }}
        public int DisallowedSpeculativePaths { get { return GetCounter<TerminatedWithDisallowedSpeculativePath>(); }}
        public int UnexplorableGotos { get { return GetCounter<TerminatedAtGotoWithUnsatisfiableTargets>(); }}

        private Dictionary<System.Type, int> Counters;

        protected int GetCounter<T>()
        {
            Debug.Assert(Counters.ContainsKey(typeof(T)), "Requested an unhandled Termination type");
            return Counters[typeof(T)];
        }

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
                // Note we don't consider a DisallowedSpeculativePath or UnExplorableGotos to be failures
            }
        }

        public int NumberOfTerminatedStates
        {
            get { return NumberOfFailures + Sucesses + DisallowedSpeculativePaths + UnexplorableGotos; }
        }

        public TerminationCounter()
        {
            this.Counters = new Dictionary<System.Type, int>();
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
            var terminationType = arg.State.TerminationType.GetType();
            Debug.Assert(Counters.ContainsKey(terminationType), "Termination type not handled!");

            var oldValue = Counters[terminationType];
            Counters[terminationType] = ++oldValue;
        }

        public void reset()
        {
            Counters.Clear();
            Counters.Add(typeof(TerminatedWithoutError), 0);
            Counters.Add(typeof(TerminatedAtFailingAssert), 0);
            Counters.Add(typeof(TerminatedAtUnsatisfiableEntryRequires), 0);
            Counters.Add(typeof(TerminatedAtFailingRequires), 0);
            Counters.Add(typeof(TerminatedAtFailingEnsures), 0);
            Counters.Add(typeof(TerminatedAtUnsatisfiableAssume), 0);
            Counters.Add(typeof(TerminatedAtUnsatisfiableEnsures), 0);
            Counters.Add(typeof(TerminatedAtUnsatisfiableAxiom), 0);
            Counters.Add(typeof(TerminatedWithDisallowedSpeculativePath), 0);
            Counters.Add(typeof(TerminatedAtGotoWithUnsatisfiableTargets), 0);
        }


        public override string ToString()
        {
            var output = "[TerminationCounter:\n";

            foreach (var terminationTypeCounterPair in Counters)
            {
                output += "  " + terminationTypeCounterPair.Key.ToString() + "=" + terminationTypeCounterPair.Value + "\n";
            }

            output += "]\n";

            return output;
        }

    }
}

