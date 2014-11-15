using NUnit.Framework;
using Microsoft.Boogie;
using Symbooglix;
using System.Collections.Generic;
using System;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldArithmeticCoercion : TestBase
    {
        [Test()]
        public void RealToInt()
        {
            var constReal = getConstantReal("5.5");
            var args = new List<Expr> { constReal };

            var artCoe = new NAryExpr(Token.NoToken, new ArithmeticCoercion(Token.NoToken, ArithmeticCoercion.CoercionType.ToInt), args);
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(artCoe);
            Assert.IsInstanceOf<LiteralExpr>(result);

            var literal = result as LiteralExpr;
            Assert.IsTrue(literal.isBigNum);
            Assert.IsTrue(literal.asBigNum.ToBigInteger == 5);
        }

        [Test()]
        public void IntToReal()
        {
            var args = new List<Expr> { getConstantInt(11) };
            var artCoe = new NAryExpr(Token.NoToken, new ArithmeticCoercion(Token.NoToken, ArithmeticCoercion.CoercionType.ToReal), args);
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(artCoe);
            Assert.IsInstanceOf<LiteralExpr>(result);

            var literal = result as LiteralExpr;
            Assert.IsTrue(literal.isBigDec);
            Assert.IsTrue(literal.asBigDec.ToString() == "11e0");
        }
    }


}

