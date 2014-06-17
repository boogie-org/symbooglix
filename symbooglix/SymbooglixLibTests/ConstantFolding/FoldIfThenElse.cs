using NUnit.Framework;
using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using symbooglix;

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
    }
}

