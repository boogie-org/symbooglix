using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;


namespace Symbooglix
{
    public class SymbolicPool
    {
        public int Count
        {
            get;
            private set;
        }

        public SymbolicPool()
        {
            Count = 0;
        }

        public SymbolicVariable getFreshSymbolic(Variable Origin)
        {
            return new SymbolicVariable("symbolic_" + (Count++).ToString(), Origin);
        }

        public SymbolicVariable getFreshSymbolic(HavocCmd cmd, int VarsIndex)
        {
            return new SymbolicVariable("symbolic_" + (Count++).ToString(), cmd, VarsIndex);
        }

    }

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

        public SymbolicVariable(string Name, Variable Origin) : base(Token.NoToken, CopyAndRename(Origin.TypedIdent, Name))
        {
            Expr = new IdentifierExpr(Token.NoToken, this);
            this.Origin = new ProgramLocation(Origin);
            this.Name = Name;
            Debug.WriteLine("Creating Symbolic " + this);
        }

        public SymbolicVariable(string Name, HavocCmd Origin, int VarsIndex) : base(Token.NoToken, CopyAndRename(Origin.Vars[VarsIndex].Decl.TypedIdent, Name))
        {
            Expr = new IdentifierExpr(Token.NoToken, this);
            this.Origin = new ProgramLocation(Origin);
            this.Name = Name;
            Debug.WriteLine("Creating Symbolic " + this);

            // Should we record VarsIndex?
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
            else
            {
                s += " Cmd:" + Origin.AsCmd.ToString().TrimEnd('\n') + ")";
            }
            return s;
        }
    }

    public class ProgramLocation
    {
        private Object Location;

        // The location is where this variable is declared
        public ProgramLocation(Variable V)
        {
            Location = (Object) V;
        }

        // The location is where this cmd is executed
        public ProgramLocation(Cmd cmd)
        {
            Location = (Object) cmd;
        }

        public bool IsVariable
        {
            get { return Location is Variable; }
        }

        public Variable AsVariable
        {
            get
            {
                if (IsVariable)
                    return Location as Variable;
                else
                    return null;
            }
        }

        public bool IsCmd
        {
            get { return Location is Cmd; }
        }

        public Cmd AsCmd
        {
            get
            {
                if (IsCmd)
                    return Location as Cmd;
                else
                    return null;
            }
        }

        public override string ToString()
        {
            if (IsVariable)
                return "[Variable] " + AsVariable.ToString();
            else if (IsCmd)
                return "[Cmd] " + AsCmd.ToString();
            else
                return "unknown";
        }
    }
}

