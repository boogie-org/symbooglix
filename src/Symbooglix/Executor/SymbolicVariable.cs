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
using System.Diagnostics;

namespace Symbooglix
{
    public class SymbolicVariable : Microsoft.Boogie.Variable
    {
        public ProgramLocation Origin
        {
            get;
            private set;
        }
        // FIXME: Need a location in the executiontrace too

        public Microsoft.Boogie.IdentifierExpr Expr
        {
            get;
            private set;
        }

        public SymbolicVariable(string name, Variable variable) : base(Token.NoToken, CopyAndRename(variable.TypedIdent, name))
        {
            Expr = new IdentifierExpr(Token.NoToken, this, /*immutable=*/ true);
            this.Origin = variable.GetProgramLocation();
            Debug.Assert(this.Origin.IsVariable, "Expected ProgramLocation to be a Variable");
            this.Name = name;
            Debug.WriteLine("Creating Symbolic " + this);
        }

        public SymbolicVariable(string name, HavocCmd cmd, int varsIndex) : base(Token.NoToken, CopyAndRename(cmd.Vars[varsIndex].Decl.TypedIdent, name))
        {
            Expr = new IdentifierExpr(Token.NoToken, this, /*immutable=*/ true);
            this.Origin = cmd.GetProgramLocation();
            Debug.Assert(this.Origin.IsCmd && ( this.Origin.AsCmd is HavocCmd ), "Expected ProgramLocation to be a HavocCmd");
            this.Name = name;
            Debug.WriteLine("Creating Symbolic " + this);

            // Should we record VarsIndex?
        }

        public SymbolicVariable(string name, Procedure proc, int modsetIndex) : base(Token.NoToken, CopyAndRename(proc.Modifies[modsetIndex].Decl.TypedIdent, name))
        {
            Expr = new IdentifierExpr(Token.NoToken, this, /*immutable*/ true);
            this.Origin = proc.GetModSetProgramLocation();
            Debug.Assert(this.Origin.IsModifiesSet, "Expected ProgramLocation to be a modset");
            this.Name = name;
            Debug.WriteLine("Creating Symbolic " + this);

            // Should we record modSetIndex?
        }

        private static Microsoft.Boogie.TypedIdent CopyAndRename(Microsoft.Boogie.TypedIdent TI, string NewName)
        {
            // HACK: We need our own TypedIdent apparently so when we print Expr we have the right name for the variable
            // instead of the name of the origin Variable.
            var copy = (Microsoft.Boogie.TypedIdent) TI.Clone();
            copy.Name = NewName;
            return copy;
        }

        public override bool IsMutable
        {
            get
            {
                if (Origin.IsVariable)
                {
                    return Origin.AsVariable.IsMutable;
                }
                else
                {
                    return true;
                }
            }
        }

        public override void Register(ResolutionContext rc)
        {
            // Do we need to do anything here?
        }

        public override string ToString()
        {
            var s = string.Format("{0}:{1} (origin ", Name, TypedIdent.Type);

            if (Origin.IsVariable)
            {
                s += " Variable: " + Origin.AsVariable + ")";
            }
            else if (Origin.IsCmd)
            {
                s += " Cmd:" + Origin.AsCmd.ToString().TrimEnd(new char[] {'\r', '\n'}) + ")";
            }
            else if (Origin.IsModifiesSet)
            {
                s += " Modset:" + Origin.AsModifiesSet.ToString();
            }
            else
            {
                throw new NotSupportedException("Unhandled origin " + Origin.ToString());
            }

            return s;
        }
    }
}

