using NUnit.Framework;
using System;
using Microsoft.Boogie;
using symbooglix;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldIff : ConstantFoldingTest
    {
        [Test()]
        public void simple()
        {
            for (int arg0 = 0; arg0 <= 1; ++arg0)
            {
                for (int arg1= 0; arg1 <=1; ++arg1)
                {
                    // (arg0 <==> arg1) == ( (arg0 ==> arg1) AND (arg1 ==> arg0) )
                    bool expected = ( !(arg0 == 1) || (arg1 == 1)) && ( !(arg1 ==1) || (arg0 ==1) ); // !arg0 OR arg1 == (arg0 ==> arg1)

                    Expr arg0Expr = getValue(arg0);
                    Expr arg1Expr = getValue(arg1);
                    Assert.IsTrue(arg0Expr is LiteralExpr);
                    Assert.IsTrue(arg1Expr is LiteralExpr);

                    var TC = new TypecheckingContext(this);
                    var CFT = new ConstantFoldingTraverser();
                    var IffExpr = Expr.Iff(arg0Expr, arg1Expr);
                    IffExpr.Typecheck(TC);

                    Expr result = CFT.Traverse(IffExpr);
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

            // (true <==> <expr>) == <expr>
            var e1 = Expr.Iff(Expr.True, consequent);
            var TC = new TypecheckingContext(this);
            e1.Typecheck(TC);

            var CFT = new ConstantFoldingTraverser();
            Expr result = CFT.Traverse(e1);
            Assert.IsTrue(result is IdentifierExpr);
            Assert.AreSame(result, consequent);

            // ( false <==> <expr> ) == NOT <expr>
            var e2 = Expr.Iff(Expr.False, consequent);
            e2.Typecheck(TC);
            result = CFT.Traverse(e2);
            Assert.IsTrue(result is NAryExpr);
            var resultAsNary = result as NAryExpr;
            Assert.IsTrue(resultAsNary.Fun is UnaryOperator);
            Assert.IsTrue(( resultAsNary.Fun as UnaryOperator ).Op == UnaryOperator.Opcode.Not);
            Assert.AreSame(resultAsNary.Args[0], consequent);
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
