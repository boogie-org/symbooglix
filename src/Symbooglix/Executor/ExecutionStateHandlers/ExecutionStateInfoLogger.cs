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
    public class ExecutionStateInfoLogger : ExecutionStateLogger
    {
        bool ShowVariables;
        bool ShowConstraints;
        public ExecutionStateInfoLogger(ExecutionStateLogger.ExecutorEventType eventToLog,
                                        bool showConstraints, bool showVariables,
                                        Predicate<ExecutionState> filterMatching = null, bool logConcurrently=true) : base(eventToLog, filterMatching, logConcurrently)
        {
            this.ShowVariables = showVariables;
            this.ShowConstraints = showConstraints;
        }

        protected override void DoTask(Executor e, ExecutionState State)
        {
            string terminatationTypeName = null;


            if (State.TerminationType == null)
                terminatationTypeName = "NonTerminated";
            else
                terminatationTypeName = State.TerminationType.GetType().ToString();

            var path = Path.Combine(Directory, ((State.Id >= 0)?State.Id.ToString():"initial") + "-" + terminatationTypeName + ".yml");
            using (var SW = new StreamWriter(path))
            {
                using (var ITW = new System.CodeDom.Compiler.IndentedTextWriter(SW, " "))
                {
                    Console.WriteLine("Logging State {0} info to {1}", State.Id, path);
                    ITW.WriteLine("# vim: set sw=1 ts=1 softtabstop=1:"); // Tell vim how to indent the YAML file.
                    State.WriteAsYAML(ITW, ShowConstraints, ShowVariables);
                }
            }
        }
    }
}

