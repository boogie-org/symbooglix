using NUnit.Framework;
using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using Symbooglix;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldIfThenElse : TestBase
    {
        [Test()]
        public void IfTrue()
        {
            var id0 = new IdentifierExpr(Token.NoToken, "foo", new BvType(8));
            var id1 = new IdentifierExpr(Token.NoToken, "bar", new BvType(8));
            Expr iteExpr = getIfThenElse(Expr.True, id0, id1);
            var TC = new TypecheckingContext(this);
            iteExpr.Typecheck(TC);

            var CFT = new ConstantFoldingTraverser();
            Expr result = CFT.Traverse(iteExpr);
            Assert.AreSame(result, id0);

        }

        [Test()]
        public void IfFalse()
        {
            var id0 = new IdentifierExpr(Token.NoToken, "foo", new BvType(8));
            var id1 = new IdentifierExpr(Token.NoToken, "bar", new BvType(8));
            Expr iteExpr = getIfThenElse(Expr.False, id0, id1);
            var TC = new TypecheckingContext(this);
            iteExpr.Typecheck(TC);

            var CFT = new ConstantFoldingTraverser();
            Expr result = CFT.Traverse(iteExpr);
            Assert.AreSame(result, id1);

        }

        public NAryExpr getIfThenElse(Expr condition, Expr resultIfTrue, Expr resultIfFalse)
        {
            // FIXME: Boogie should have a static method for building these
            return new NAryExpr(Token.NoToken, new IfThenElse(Token.NoToken), new List<Expr> { condition, resultIfTrue, resultIfFalse });
        }

        [Test()]
        public void IfConditionThenConditionAndElseFalse()
        {
            var v = new IdentifierExpr(Token.NoToken, new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "v", Microsoft.Boogie.Type.Bool)));
            var ifThenElse = builder.IfThenElse(v, v, builder.ConstantBool(false));

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(ifThenElse);
            Assert.AreSame(v, result);
        }

        [Test()]
        public void IfNotConditionThenConditionElseTrue()
        {
            var v = new IdentifierExpr(Token.NoToken, new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "v", Microsoft.Boogie.Type.Bool)));
            var ifThenElse = builder.IfThenElse(builder.Not(v), v, builder.ConstantBool(true));

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(ifThenElse);
            Assert.AreSame(v, result);
        }

        [Test()]
        public void IfConditionThenTrueElseCondition()
        {
            var v = new IdentifierExpr(Token.NoToken, new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "v", Microsoft.Boogie.Type.Bool)));
            var y = new IdentifierExpr(Token.NoToken, new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "y", Microsoft.Boogie.Type.Bool)));
            var vNotEqy = builder.NotEq(v, y);

            var ife = builder.IfThenElse (vNotEqy, builder.ConstantBool(true), vNotEqy);
            Assert.AreNotEqual(ife, vNotEqy);

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(ife);
            Assert.AreSame(vNotEqy, result);
        }
    }
}

