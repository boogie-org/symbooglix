using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;


namespace symbooglix
{
    public class SymbolicPool
    {
        // FIXME: We are preventing garbage collection by holding on to these
        public HashSet<SymbolicVariable> symbolics
        {
            get;
            private set;
        }

        public int count
        {
            get;
            private set;
        }

        public SymbolicPool()
        {
            symbolics = new HashSet<SymbolicVariable>();
            count = 0;
        }

        public SymbolicVariable getFreshSymbolic(Microsoft.Boogie.TypedIdent t)
        {
            TypedIdent modifiedT = (TypedIdent) t.Clone(); // Need a copy so we can modify its name without affecting the original source
            modifiedT.Name = "symbolic_" + count.ToString();
            var s = new SymbolicVariable(modifiedT);
            symbolics.Add(s);
            ++count;
            Debug.WriteLine("Created new symbolic " + s);
            return s;
        }

    }

    public class SymbolicVariable
    {
        public Microsoft.Boogie.TypedIdent typedIdentifier
        {
            get;
            private set;
        }

        public Microsoft.Boogie.IdentifierExpr expr
        {
            get;
            private set;
        }

        public string getName()
        {
            return typedIdentifier.Name;
        }

        public Microsoft.Boogie.Type getType()
        {
            return typedIdentifier.Type;
        }


        public SymbolicVariable(TypedIdent t)
        {
            // Use arbitrary constant to represent symbolic
            // The constant gets its name from the TypeIdent, do we want this??
            var c = new Constant(Token.NoToken, t, false);
            expr = new IdentifierExpr(Token.NoToken, c);
            typedIdentifier = t;
        }

        public override string ToString()
        {
            return string.Format("[SymbolicVariable: {0}:{1}]", getName(), getType());
        }

    }
}

