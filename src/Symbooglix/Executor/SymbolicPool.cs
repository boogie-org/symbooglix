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

        // Symbolic from a procedure's modeset
        public SymbolicVariable getFreshSymbolic(Procedure proc, int modSetIndex)
        {
            return new SymbolicVariable("symbolic_" + (Count++).ToString(), proc, modSetIndex);
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

        public SymbolicVariable(string Name, Variable variable) : base(Token.NoToken, CopyAndRename(variable.TypedIdent, Name))
        {
            Expr = new IdentifierExpr(Token.NoToken, this);
            this.Origin = variable.GetMetatdata<ProgramLocation>( (int) Annotation.AnnotationIndex.PROGRAM_LOCATION);
            this.Name = Name;
            Debug.WriteLine("Creating Symbolic " + this);
        }

        public SymbolicVariable(string Name, HavocCmd cmd, int VarsIndex) : base(Token.NoToken, CopyAndRename(cmd.Vars[VarsIndex].Decl.TypedIdent, Name))
        {
            Expr = new IdentifierExpr(Token.NoToken, this);
            this.Origin = cmd.GetMetatdata<ProgramLocation>( (int) Annotation.AnnotationIndex.PROGRAM_LOCATION);
            this.Name = Name;
            Debug.WriteLine("Creating Symbolic " + this);

            // Should we record VarsIndex?
        }

        public SymbolicVariable(string Name, Procedure Origin, int modsetIndex) : base(Token.NoToken, CopyAndRename(Origin.Modifies[modsetIndex].Decl.TypedIdent, Name))
        {
            Expr = new IdentifierExpr(Token.NoToken, this);
            // FIXME: Don't create a new ProgramLocation, instead have ProgramLocationAnnotation pass add it so we can retrieve it here
            this.Origin = new ProgramLocation(new ModifiesSet(Origin));
            this.Name = Name;
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
                s += " Cmd:" + Origin.AsCmd.ToString().TrimEnd('\n') + ")";
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

