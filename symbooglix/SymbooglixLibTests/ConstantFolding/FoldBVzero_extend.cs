using NUnit.Framework;
using System;
using symbooglix;
using Microsoft.Boogie;
using System.Collections.Generic;
using Microsoft.Basetypes;


namespace SymbooglixLibTests
{
    [TestFixture()]
    public class FoldBVzero_extend : IErrorSink
    {
        [Test()]
        public void Simple()
        {
            var inputBV = new LiteralExpr(Token.NoToken, BigNum.FromInt(7), 4); // 7bv4
            Microsoft.Boogie.Type[] argTypes = {BvType.GetBvType(4) };
            var zeroExtend = CreateBVBuiltIn("BV4_ZEXT8", "zero_extend 8", BvType.GetBvType(8), argTypes);

            var args = new List<Expr>();
            args.Add(inputBV);
            var nary = new NAryExpr(Token.NoToken, zeroExtend, args);
            var TC = new TypecheckingContext(this);
            nary.Typecheck(TC);

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(nary);
            Assert.IsTrue(result is LiteralExpr);

            var literal = result as LiteralExpr;
            Assert.IsTrue(literal.isBvConst);
            Assert.IsTrue(literal.asBvConst.Bits == 8);
            Assert.IsTrue(literal.asBvConst.Value == BigNum.FromInt(7));
        }

        public FunctionCall CreateBVBuiltIn(string Name, string Builtin, Microsoft.Boogie.Type returnType, Microsoft.Boogie.Type[] argTypes)
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

        public void Error(IToken tok, string msg)
        {
            Assert.Fail(msg);
        }
    }
}

