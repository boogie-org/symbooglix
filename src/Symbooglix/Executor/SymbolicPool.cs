using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;


namespace Symbooglix
{
    public class SymbolicPool
    {
        Dictionary<String, int> SuffixStore;
        public int Count
        {
            get;
            private set;
        }

        public SymbolicPool()
        {
            SuffixStore = new Dictionary<string, int>();
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

        public SymbolicVariable getFreshSymbolic(Variable Origin)
        {
            return new SymbolicVariable(GetNewSymbolicVariableName(Origin), Origin);
        }

        public SymbolicVariable getFreshSymbolic(HavocCmd cmd, int varsIndex)
        {
            return new SymbolicVariable(GetNewSymbolicVariableName(cmd, varsIndex), cmd, varsIndex);
        }

        // Symbolic from a procedure's modeset
        public SymbolicVariable getFreshSymbolic(Procedure proc, int modSetIndex)
        {
            return new SymbolicVariable(GetNewSymbolicVariableName(proc, modSetIndex), proc, modSetIndex);
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
            Expr = new IdentifierExpr(Token.NoToken, this, /*immutable=*/ true);
            this.Origin = variable.GetMetadata<ProgramLocation>( (int) Annotation.AnnotationIndex.PROGRAM_LOCATION);
            this.Name = Name;
            Debug.WriteLine("Creating Symbolic " + this);
        }

        public SymbolicVariable(string Name, HavocCmd cmd, int VarsIndex) : base(Token.NoToken, CopyAndRename(cmd.Vars[VarsIndex].Decl.TypedIdent, Name))
        {
            Expr = new IdentifierExpr(Token.NoToken, this, /*immutable=*/ true);
            this.Origin = cmd.GetMetadata<ProgramLocation>( (int) Annotation.AnnotationIndex.PROGRAM_LOCATION);
            this.Name = Name;
            Debug.WriteLine("Creating Symbolic " + this);

            // Should we record VarsIndex?
        }

        public SymbolicVariable(string Name, Procedure Origin, int modsetIndex) : base(Token.NoToken, CopyAndRename(Origin.Modifies[modsetIndex].Decl.TypedIdent, Name))
        {
            Expr = new IdentifierExpr(Token.NoToken, this, /*immutable*/ true);
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

