using System;
using Microsoft.Boogie;
using NUnit.Framework;
using System.Collections.Generic;
using Microsoft.Basetypes;

namespace ConstantFoldingTests
{
    public class TestBase : IErrorSink
    {
        public TestBase()
        {
            SymbooglixLibTests.SymbooglixTest.setupDebug();
        }

        public void Error (IToken tok, string msg)
        {
            Assert.Fail(msg);
        }

        public static FunctionCall CreateBVBuiltIn(string Name, string Builtin, Microsoft.Boogie.Type returnType, Microsoft.Boogie.Type[] argTypes)
        {
            var funcCall = CreateFunctionCall(Name, returnType, argTypes);
            funcCall.Func.AddAttribute("bvbuiltin", new string[] { Builtin });
            return funcCall;
        }

        public static FunctionCall CreateFunctionCall(string Name, Microsoft.Boogie.Type returnType, Microsoft.Boogie.Type[] argTypes)
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

        public static LiteralExpr getConstantInt(int value)
        {
            return new LiteralExpr(Token.NoToken, BigNum.FromInt(value));
        }

        public static LiteralExpr getConstantReal(string value)
        {
            return new LiteralExpr(Token.NoToken, BigDec.FromString(value));
        }

    }
}

