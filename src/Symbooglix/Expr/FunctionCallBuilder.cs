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
using System.Collections.Generic;
using System.Collections.Concurrent;
using Microsoft.Boogie;
using System.Diagnostics;

namespace Symbooglix
{
    public class FunctionCallBuilder
    {
        public FunctionCallBuilder()
        {
        }

        private ConcurrentDictionary<string, FunctionCall> CachedUninterpretedFunctionCalls = new ConcurrentDictionary<string, FunctionCall>();
        public FunctionCall CreateCachedUninterpretedFunctionCall(string name, Microsoft.Boogie.Type returnType, IList<Microsoft.Boogie.Type> argTypes)
        {
            FunctionCall functionCall = null;
            try
            {
                functionCall = CachedUninterpretedFunctionCalls[name];

                // It is very important that we check the types match here. Functions cannot be overloaded
                // so we cannot allow functions of the same to exist that have different types

                Debug.Assert(functionCall.Func.OutParams.Count == 1, "Stored functionCall has wrong number of out params");

                // Check all types match
                if (!functionCall.Func.OutParams[0].TypedIdent.Type.Equals(returnType))
                {
                    throw new ExprTypeCheckException("The cached functionCall's return type does not match the requested");
                }

                if (functionCall.Func.InParams.Count != argTypes.Count)
                {
                    throw new ExprTypeCheckException("The cached functionCall has a different number of arguments than what was requested");
                }

                for (int index=0; index < argTypes.Count; ++index)
                {
                    if (!functionCall.Func.InParams[index].TypedIdent.Type.Equals(argTypes[index]))
                    {
                        throw new ExprTypeCheckException("The cached functionCall has different type from what was requested at arg " + index.ToString());
                    }
                }
            }
            catch (KeyNotFoundException)
            {
                functionCall = CreateUninterpretedFunctionCall(name, returnType, argTypes);
                CachedUninterpretedFunctionCalls[name] = functionCall;
            }
            return functionCall;
        }

        // No caching
        public FunctionCall CreateUninterpretedFunctionCall(string Name, Microsoft.Boogie.Type returnType, IList<Microsoft.Boogie.Type> argTypes)
        {
            var returnVar = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", returnType), false);
            var vars = new List<Variable>();
            foreach (var T in argTypes)
            {
                vars.Add( new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "",T), true));
            }

            // Finally build the function and the function call
            var funcCall = new FunctionCall(new Function(Token.NoToken, Name, vars, returnVar));
            return funcCall;
        }
    }
}

