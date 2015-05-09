using System;
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Boogie;
using BPLType = Microsoft.Boogie.Type;

namespace Symbooglix
{
    public class MapProxy
    {
        private Expr ExpressionRepresentation;
        BPLType MapType;

        public MapProxy(Expr initialValue)
        {
            ExpressionRepresentation = initialValue;
            this.MapType = initialValue.Type;

            if (!this.MapType.IsMap)
                throw new ArgumentException("Must be map type");
        }

        // Might avoid map store flushing
        public Expr ReadMapAt(IList<Expr> indicies)
        {
            throw new NotImplementedException();
        }

        // Might avoid map store flushing
        public Expr WriteMapAt(IList<Expr> indicies, Expr value)
        {
            throw new NotImplementedException();
        }

        // Will force map store flush
        public Expr Read()
        {
            // TODO: Implement flushing

            return ExpressionRepresentation;
        }

        // Will force map store flush
        public void Write(Expr newValue)
        {
            // TODO: Implement flushing

            if (!newValue.Type.Equals(this.MapType))
                throw new ArgumentException("newValue must have correct map type");

            ExpressionRepresentation = newValue;
        }

        // FIXME: Implement smarter copy on write mechanism
        public MapProxy Clone()
        {
            var other = (MapProxy) this.MemberwiseClone();
            return other;
        }
    }
}

