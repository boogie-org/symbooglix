using NUnit.Framework;
using Microsoft.Boogie;
using Symbooglix;
using System;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldNeg : TestBase
    {
        [Test()]
        public void Integer()
        {
            var negation = Expr.Neg(getConstantInt(1));
            var CFT = new ConstantFoldingTraverser();
            var e = CFT.Traverse(negation);

            Assert.IsInstanceOfType(typeof(LiteralExpr), e);
            var literal = e as LiteralExpr;
            Assert.IsTrue(literal.isBigNum);
            Assert.AreEqual(literal.asBigNum.ToInt, -1);
        }

        [Test()]
        public void IntegerDoubleNegative()
        {
            var negation = Expr.Neg(Expr.Neg(getConstantInt(1)));
            var CFT = new ConstantFoldingTraverser();
            var e = CFT.Traverse(negation);

            Assert.IsInstanceOfType(typeof(LiteralExpr), e);
            var literal = e as LiteralExpr;
            Assert.IsTrue(literal.isBigNum);
            Assert.AreEqual(literal.asBigNum.ToInt, 1);
        }

        [Test()]
        public void Real()
        {
            var negation = Expr.Neg(getConstantReal("2.0"));
            var CFT = new ConstantFoldingTraverser();
            var e = CFT.Traverse(negation);

            Assert.IsInstanceOfType(typeof(LiteralExpr), e);
            var literal = e as LiteralExpr;
            Assert.IsTrue(literal.isBigDec);
            Assert.AreEqual(literal.asBigDec.ToString(), "-2e0");
        }

        [Test()]
        public void RealDoubleNegative()
        {
            var negation = Expr.Neg(Expr.Neg(getConstantReal("2.0")));
            var CFT = new ConstantFoldingTraverser();
            var e = CFT.Traverse(negation);

            Assert.IsInstanceOfType(typeof(LiteralExpr), e);
            var literal = e as LiteralExpr;
            Assert.IsTrue(literal.isBigDec);
            Assert.AreEqual(literal.asBigDec.ToString(), "2e0");
        }
    }
}

