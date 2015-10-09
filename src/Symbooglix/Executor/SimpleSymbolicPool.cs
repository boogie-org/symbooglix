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
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;


namespace Symbooglix
{
    public class SimpleSymbolicPool :  ISymbolicPool
    {
        Dictionary<String, int> SuffixStore;
        public int Count
        {
            get;
            private set;
        }

        public SimpleSymbolicPool()
        {
            SuffixStore = new Dictionary<string, int>();
            Count = 0;
        }

        public readonly string Prefix = "~sb_";

        protected string GetNewSymbolicVariableName(Variable Origin)
        {
            int num = 0;

            string key = Origin.TypedIdent.Name;
            try
            {
                num = SuffixStore[key];
            }
            catch (KeyNotFoundException)
            {
                num = 0;
                SuffixStore[key] = num;
            }

            // Increment the number now that we've used it
            SuffixStore[key] = num +1;

            return Prefix + key + "_" + num.ToString();
        }

        protected string GetNewSymbolicVariableName(HavocCmd havocCmd, int varsIndex)
        {
            return GetNewSymbolicVariableName(havocCmd.Vars[varsIndex].Decl);
        }

        protected string GetNewSymbolicVariableName(Procedure proc, int modSetIndex)
        {
            return GetNewSymbolicVariableName(proc.Modifies[modSetIndex].Decl);
        }

        public SymbolicVariable GetFreshSymbolic(Variable Origin, ExecutionState owner)
        {
            ++Count;
            return new SymbolicVariable(GetNewSymbolicVariableName(Origin), Origin);
        }

        public SymbolicVariable GetFreshSymbolic(HavocCmd cmd, int varsIndex, ExecutionState owner)
        {
            ++Count;
            return new SymbolicVariable(GetNewSymbolicVariableName(cmd, varsIndex), cmd, varsIndex);
        }

        // Symbolic from a procedure's modeset
        public SymbolicVariable GetFreshSymbolic(Procedure proc, int modSetIndex, ExecutionState owner)
        {
            ++Count;
            return new SymbolicVariable(GetNewSymbolicVariableName(proc, modSetIndex), proc, modSetIndex);
        }

        public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
        {
            TW.WriteLine("name : \"{0}\"", this.GetType().ToString());
            TW.WriteLine("count: {0}", this.Count);
        }
    }
}

