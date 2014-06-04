using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;


namespace symbooglix
{
    public class SymbolicPool
    {
        public int count
        {
            get;
            private set;
        }

        public SymbolicPool()
        {
            count = 0;
        }

        public SymbolicVariable getFreshSymbolic(Variable Origin)
        {
            return new SymbolicVariable("symbolic_" + (count++).ToString(), Origin);
        }

        public SymbolicVariable getFreshSymbolic(HavocCmd cmd, int VarsIndex)
        {
            return new SymbolicVariable("symbolic_" + (count++).ToString(), cmd, VarsIndex);
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

        public Microsoft.Boogie.IdentifierExpr expr
        {
            get;
            private set;
        }

        public SymbolicVariable(string Name, Variable Origin) : base(Token.NoToken, CopyAndRename(Origin.TypedIdent, Name))
        {
            expr = new IdentifierExpr(Token.NoToken, this);
            this.Origin = new ProgramLocation(Origin);
            this.Name = Name;
            Debug.WriteLine("Creating Symbolic " + this);
        }

        public SymbolicVariable(string Name, HavocCmd Origin, int VarsIndex) : base(Token.NoToken, CopyAndRename(Origin.Vars[VarsIndex].Decl.TypedIdent, Name))
        {
            expr = new IdentifierExpr(Token.NoToken, this);
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
        private Object location;

        // The location is where this variable is declared
        public ProgramLocation(Variable V)
        {
            location = (Object) V;
        }

        // The location is where this cmd is executed
        public ProgramLocation(Cmd cmd)
        {
            location = (Object) cmd;
        }

        public bool IsVariable
        {
            get { return location is Variable; }
        }

        public Variable AsVariable
        {
            get
            {
                if (IsVariable)
                    return location as Variable;
                else
                    return null;
            }
        }

        public bool IsCmd
        {
            get { return location is Cmd; }
        }

        public Cmd AsCmd
        {
            get
            {
                if (IsCmd)
                    return location as Cmd;
                else
                    return null;
            }
        }
    }
}

