using NUnit.Framework;
using System;
using Microsoft.Basetypes;
using Microsoft.Boogie;
using Symbooglix;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldSub : TestBase
    {
        [Test()]
        public void NegativeInts()
        {
            var sub = Expr.Sub(TestBase.getConstantInt(-1), TestBase.getConstantInt(-2));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(sub);
            Assert.IsInstanceOfType(typeof(LiteralExpr), result);
            var resultAsLiteral = result as LiteralExpr;
            Assert.IsTrue(resultAsLiteral.isBigNum);
            Assert.IsTrue(resultAsLiteral.asBigNum == BigNum.FromInt(1));
        }

        [Test()]
        public void PositiveInts()
        {
            var sub = Expr.Sub(TestBase.getConstantInt(1), TestBase.getConstantInt(2));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(sub);
            Assert.IsInstanceOfType(typeof(LiteralExpr), result);
            var resultAsLiteral = result as LiteralExpr;
            Assert.IsTrue(resultAsLiteral.isBigNum);
            Assert.IsTrue(resultAsLiteral.asBigNum == BigNum.FromInt(-1));
        }

        [Test()]
        public void NegativeReals()
        {
            var sub = Expr.Sub(TestBase.getConstantReal("-1.5"), TestBase.getConstantReal("-2.5"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(sub);
            Assert.IsInstanceOfType(typeof(LiteralExpr), result);
            var resultAsLiteral = result as LiteralExpr;
            Assert.IsTrue(resultAsLiteral.isBigDec);
            Assert.AreEqual(BigDec.FromString("1.0"), resultAsLiteral.asBigDec);
        }

        [Test()]
        public void PositiveReals()
        {
            var sub = Expr.Sub(TestBase.getConstantReal("1.5"), TestBase.getConstantReal("2.6"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(sub);
            Assert.IsInstanceOfType(typeof(LiteralExpr), result);
            var resultAsLiteral = result as LiteralExpr;
            Assert.IsTrue(resultAsLiteral.isBigDec);
            Assert.AreEqual(BigDec.FromString("-1.1"), resultAsLiteral.asBigDec);
        }
    }
}

