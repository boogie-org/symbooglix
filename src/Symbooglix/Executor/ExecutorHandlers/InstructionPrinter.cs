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
    public class InstructionPrinter : IExecutorEventHandler
    {
        TextWriter TW;
        public InstructionPrinter(TextWriter TW)
        {
            this.TW = TW;
        }

        private void handle(Object executor, Executor.InstructionVisitEventArgs instructionVisitEventArgs)
        {
            var loc = instructionVisitEventArgs.Location;
            TW.WriteLine(loc.FileName + ":" + loc.LineNumber + ": " + loc.ToString().TrimEnd('\n'));
        }

        public void Connect(Executor e)
        {
            e.InstructionVisited += handle;
        }

        public void Disconnect(Executor e)
        {
            e.InstructionVisited -= handle;
        }
    }
}

