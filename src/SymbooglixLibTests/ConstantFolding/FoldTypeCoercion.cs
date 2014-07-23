using NUnit.Framework;
using Microsoft.Boogie;
using Symbooglix;
using System.Collections.Generic;
using System;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldTypeCoercion : TestBase
    {
        [Test()]
        public void Trivial()
        {
            var functionCall = CreateFunctionCall("foo", BasicType.Bool, new Microsoft.Boogie.Type[] { BasicType.Int });
            Assert.IsNotNull(functionCall);

            var functionNAryExpr = new NAryExpr(Token.NoToken, functionCall, new List<Expr>() { getConstantInt(5)});
            Assert.IsNotNull(functionNAryExpr);

            // Now wrap this in a trivial TypeCoercion
            var expr = Expr.CoerceType(Token.NoToken, functionNAryExpr, BasicType.Bool);
            Assert.IsNotNull(expr);

            expr.Typecheck(new TypecheckingContext(this));

            var CFT = new ConstantFoldingTraverser();
            var newExpr = CFT.Traverse(expr);


            Assert.AreSame(functionNAryExpr, newExpr);
        }


    }
}

