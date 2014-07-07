using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Symbooglix;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldImpl : TestBase
    {
        [Test()]
        public void simple()
        {
            for (int arg0 = 0; arg0 <= 1; ++arg0)
            {
                for (int arg1= 0; arg1 <=1; ++arg1)
                {
                    bool expected = !(arg0 == 1) || (arg1 == 1); // !arg0 OR arg1 == (arg0 ==> arg1)

                    Expr arg0Expr = getValue(arg0);
                    Expr arg1Expr = getValue(arg1);
                    Assert.IsTrue(arg0Expr is LiteralExpr);
                    Assert.IsTrue(arg1Expr is LiteralExpr);

                    var TC = new TypecheckingContext(this);
                    var CFT = new ConstantFoldingTraverser();
                    var ImplExpr = Expr.Imp(arg0Expr, arg1Expr);
                    ImplExpr.Typecheck(TC);

                    Expr result = CFT.Traverse(ImplExpr);
                    result.Typecheck(TC);
                    Assert.IsTrue(result is LiteralExpr);
                    var resultAsLiteral = result as LiteralExpr;

                    if (expected)
                        Assert.IsTrue(resultAsLiteral.IsTrue);
                    else
                        Assert.IsTrue(resultAsLiteral.IsFalse);
                }
            }
        }

        [Test()]
        public void nonConstantConsequent()
        {
            Expr consequent = new IdentifierExpr(Token.NoToken, "foo", Expr.True.Type); // Boolean

            // (true ==> <expr>) == <expr>
            var e1 = Expr.Imp(Expr.True, consequent);
            var TC = new TypecheckingContext(this);
            e1.Typecheck(TC);

            var CFT = new ConstantFoldingTraverser();
            Expr result = CFT.Traverse(e1);
            Assert.IsTrue(result is IdentifierExpr);
            Assert.AreSame(result, consequent);

            // ( false ==> <expr> ) == true
            var e2 = Expr.Imp(Expr.False, consequent);
            e2.Typecheck(TC);
            result = CFT.Traverse(e2);
            Assert.IsTrue(result is LiteralExpr);
            Assert.IsTrue(( result as LiteralExpr ).IsTrue);
        }

        public Expr getValue(int v)
        {
            switch (v)
            {
                case 0:
                    return Expr.False;
                default:
                    return Expr.True;
            }
        }
    }
}
