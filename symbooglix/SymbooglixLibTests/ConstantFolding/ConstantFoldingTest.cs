using System;
using Microsoft.Boogie;
using NUnit.Framework;
using System.Collections.Generic;

namespace SymbooglixLibTests
{
    public class ConstantFoldingTest : IErrorSink
    {
        public ConstantFoldingTest()
        {
            SymbooglixTest.setupDebug();
        }

        public void Error (IToken tok, string msg)
        {
            Assert.Fail(msg);
        }

        public static FunctionCall CreateBVBuiltIn(string Name, string Builtin, Microsoft.Boogie.Type returnType, Microsoft.Boogie.Type[] argTypes)
        {
            var returnVar = new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "", returnType), false);
            var vars = new List<Variable>();
            foreach (var T in argTypes)
            {
                vars.Add( new Formal(Token.NoToken, new TypedIdent(Token.NoToken, "",T), true));
            }

            // Finally build the function
            var func = new Function(Token.NoToken, Name, vars, returnVar);
            func.AddAttribute("bvbuiltin", new string[] { Builtin });
            var funcCall = new FunctionCall(func);
            return funcCall;
        }

    }
}

