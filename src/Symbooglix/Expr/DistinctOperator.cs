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
    // DistinctExpr would be nicer but that would require changes to the StandardVisitor which I wouldn't
    // want in upstream Boogie.
    // So instead we use NAryExpr instead and have a custom operator. It's kind of clumsy though
    // because we need to pass the number of arguments to this class because the list lives in NAryExpr
    // rather than this class
    public class DistinctOperator : IAppliable
    {
        IToken Token;
        public DistinctOperator(IToken token, int numberOfExprs)
        {
            if (numberOfExprs < 1)
                throw new ArgumentException("numberOfExpr must be >= 2");

            ArgumentCount = numberOfExprs;
            Token = token;
        }

        public void Emit(IList<Expr> args, TokenTextWriter stream, int contextBindingStrength, bool fragileContext)
        {
            Debug.Assert(args.Count == ArgumentCount);

            // TODO: Don't ignore contextBindingStrength and fragileContext
            stream.SetToken(ref this.Token);
            var popRequired = stream.push(FunctionName);
            stream.Write(this.FunctionName);
            stream.Write("(");
            for (int index = 0; index < args.Count; ++index)
            {
                args[index].Emit(stream, contextBindingStrength, fragileContext);

                if (index < ( args.Count - 1 ))
                    stream.Write(", ");
            }

            stream.Write(")");
            stream.pop(popRequired);
        }

        public void Resolve(ResolutionContext rc, Expr subjectForErrorReporting)
        {
        }

        public Microsoft.Boogie.Type Typecheck(IList<Expr> args, out TypeParamInstantiation tpInstantiation, TypecheckingContext tc)
        {
            Debug.Assert(args.Count == ArgumentCount);
            // We can assume the expressions in args have already been type checked for us by NAryExpr.TypeCheck()

            // I'm not sure if this is right
            tpInstantiation = SimpleTypeParamInstantiation.EMPTY;
            var firstExpr = args[0];
            for (int index = 1; index < args.Count; ++index)
            {
                Debug.Assert(args[index].Type != null);
                if (!firstExpr.Type.Unify(args[index].Type))
                {
                    // Type checking failed
                    tc.Error(Token, String.Format("Failed to unify type {0} with {1} (argument index {2}",
                                           firstExpr.Type.ToString(), args[index].Type.ToString(), index));
                    return null;
                }
            }

            return this.ShallowType(args);
        }

        public Microsoft.Boogie.Type ShallowType(IList<Expr> args)
        {
            Debug.Assert(args.Count == ArgumentCount);
            return BasicType.Bool;
        }

        public T Dispatch<T>(IAppliableVisitor<T> visitor)
        {
            throw new NotImplementedException();
        }

        public string FunctionName
        {
            get { return "distinct"; }
        }

        public int ArgumentCount
        {
            get;
            private set;
        }

        public override bool Equals(object obj)
        {
            if (obj == null)
                return false;
            if (!(obj is DistinctOperator))
                return false;

            return true;
        }

        public override int GetHashCode()
        {
            // TODO: Is this a good choice?
            return 13;
        }
    }
}

