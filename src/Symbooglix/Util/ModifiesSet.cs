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
using System.Linq;

namespace Symbooglix
{
    // This is a convenient class for use
    // by ProgramLocation
    public class ModifiesSet
    {
        public Procedure Proc
        {
            get;
            private set;
        }

        public IList<IdentifierExpr> Identifiers
        {
            get { return Proc.Modifies; }
        }

        public IEnumerable<Variable> Variables
        {
            get { return Proc.Modifies.Select(i => i.Decl); }
        }

        public ModifiesSet(Procedure proc)
        {
            this.Proc = proc;
        }

        public override string ToString()
        {
            string info = "[Modifies set] ";
            if (Proc.Modifies.Count == 0)
                return info + " Empty set";
            else
            {
                foreach (var id in Proc.Modifies)
                    info += id.ToString() + ", ";
            }

            return info;
        }
    }
}

