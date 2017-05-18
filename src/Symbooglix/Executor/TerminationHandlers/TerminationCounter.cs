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
using System;
using System.Diagnostics;
using System.Collections.Generic;
using System.IO;

namespace Symbooglix
{
    public class TerminationCounter : IExecutorEventHandler, Util.IYAMLWriter
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
        public int DisallowedPathDepths { get { return GetCounter<TerminatedWithDisallowedExplicitBranchDepth>(); } }
        public int UnsatsifiableUniqueConstants { get { return GetCounter<TerminatedWithUnsatisfiableUniqueAttribute>(); }}
        public int DisallowedLoopDepths { get { return GetCounter<TerminatedWithDisallowedLoopBound>(); }}

        private Dictionary<System.Type, int> Counters;

        public enum CountType
        {
            ONLY_NON_SPECULATIVE,
            ONLY_SPECULATIVE,
            BOTH,
        }

        public readonly CountType TheCountType;

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
                UnsatisfiableEnsures +
                UnsatisfiableAxioms +
                UnsatsifiableUniqueConstants;
                // Note we don't consider a UnsatisfiableAssumes, DisallowedSpeculativePath or UnExplorableGotos or DisallowedPathDepths to be failures
            }
        }

        public int NumberOfTerminatedStates
        {
            get { return NumberOfFailures + Sucesses + UnsatisfiableAssumes + DisallowedSpeculativePaths + UnexplorableGotos + DisallowedPathDepths; }
        }

        public TerminationCounter(CountType countType = CountType.BOTH)
        {
            this.TheCountType = countType;
            this.Counters = new Dictionary<System.Type, int>();
            reset();
        }

        public virtual void Connect(Executor e)
        {
            e.StateTerminated += this.handle;
        }

        public virtual void Disconnect(Executor e)
        {
            e.StateTerminated -= this.handle;
        }

        protected void handle(Object executor, Executor.ExecutionStateEventArgs arg)
        {
            var terminationType = arg.State.TerminationType.GetType();
            var isSpeculative = arg.State.Speculative;
            Debug.Assert(Counters.ContainsKey(terminationType), "Termination type not handled!");

            var oldValue = Counters[terminationType];

            switch (TheCountType)
            {
                case CountType.BOTH:
                    goto doCount;
                case CountType.ONLY_SPECULATIVE:
                    if (isSpeculative)
                        goto doCount;
                    break;
                case CountType.ONLY_NON_SPECULATIVE:
                    if (!isSpeculative)
                        goto doCount;
                    break;
                doCount:
                    Counters[terminationType] = ++oldValue;
                    break;
                default:
                    throw new InvalidOperationException("Unsupported count type");
            }

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
            Counters.Add(typeof(TerminatedWithDisallowedExplicitBranchDepth), 0);
            Counters.Add(typeof(TerminatedWithDisallowedLoopBound), 0);
            Counters.Add(typeof(TerminatedWithUnsatisfiableUniqueAttribute), 0);
        }


        public override string ToString()
        {
            var output = "[TerminationCounter:\n";

            foreach (var terminationTypeCounterPair in Counters)
            {
                output += "  " + StripPrefix(terminationTypeCounterPair.Key.ToString()) + "=" + terminationTypeCounterPair.Value + "\n";
            }

            output += "]\n";

            return output;
        }


        private string StripPrefix(string original)
        {
            int dotPosition = original.IndexOf('.');
            Debug.Assert(dotPosition != -1, "Dot was not found");
            return original.Substring(dotPosition +1);
        }

        public void WriteAsGnuPlotData(TextWriter TW)
        {
            TW.WriteLine("# Load with GNUPlot");
            TW.WriteLine("#<TerminationType> <Counters>");

            foreach (var terminationTypeCounterPair in Counters)
            {
                TW.WriteLine(StripPrefix(terminationTypeCounterPair.Key.ToString()) + " " + terminationTypeCounterPair.Value);
            }
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            TW.WriteLine("# Termination Counter ({0}) info", TheCountType.ToString());
            foreach (var terminationTypeCounterPair in Counters)
            {
                TW.WriteLine("{0}: {1}", StripPrefix(terminationTypeCounterPair.Key.ToString()), terminationTypeCounterPair.Value.ToString());
            }
        }

    }
}

