//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using System.IO;

namespace Symbooglix
{
    public class CallPrinter : IExecutorEventHandler
    {
        private TextWriter TW;
        public CallPrinter(TextWriter TW)
        {
            this.TW = TW;
        }

        private void handle(Object executor, Executor.EnterImplementationEventArgs ea)
        {
            TW.Write("Entering: " + ea.Impl.Name + "(");

            if (ea.Args == null)
                TW.Write("...");
            else
            {
                for (int index=0; index < ea.Args.Count; ++index)
                {
                    TW.Write(ea.Args[index]);

                    if (index < ( ea.Args.Count - 1 ))
                        TW.Write(", ");
                }
            }

            TW.WriteLine(")");
        }

        private void handle(Object executor, Executor.LeaveImplementationEventArgs ea)
        {
            TW.WriteLine("Leaving: " + ea.Impl.Name + "(...)");
        }

        private void handle(Object executor, Executor.EnterProcedureEventArgs ea)
        {
            TW.Write("Entering: " + ea.Proc.Name + "(");

            for (int index=0; index < ea.Args.Count; ++index)
            {
                TW.Write(ea.Args[index]);

                if (index < ( ea.Args.Count - 1 ))
                    TW.Write(", ");
            }

            TW.WriteLine(")");
        }

        private void handle(Object executor, Executor.LeaveProcedureEventArgs ea)
        {
            TW.WriteLine("Leaving: " + ea.Proc.Name + "(...)");
        }

        public void Connect(Executor e)
        {
            e.ImplementationEntered += handle;
            e.ImplementationLeft += handle;
            e.ProcedureEntered += handle;
            e.ProcedureLeft += handle;
        }

        public void Disconnect (Executor e)
        {
            e.ImplementationEntered -= handle;
            e.ImplementationLeft -= handle;
            e.ProcedureEntered -= handle;
            e.ProcedureLeft -= handle;
        }
    }
}

