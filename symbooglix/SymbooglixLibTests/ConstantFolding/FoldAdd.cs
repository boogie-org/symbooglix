using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using Symbooglix;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldAdd : TestBase
    {
        [Test()]
        public void NegativeInts()
        {
            var add = Expr.Add(TestBase.getConstantInt(-1), TestBase.getConstantInt(-2));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(add);
            Assert.IsInstanceOfType(typeof(LiteralExpr), result);
            var resultAsLiteral = result as LiteralExpr;
            Assert.IsTrue(resultAsLiteral.isBigNum);
            Assert.IsTrue(resultAsLiteral.asBigNum == BigNum.FromInt(-3));
        }

        [Test()]
        public void PositiveInts()
        {
            var add = Expr.Add(TestBase.getConstantInt(1), TestBase.getConstantInt(2));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(add);
            Assert.IsInstanceOfType(typeof(LiteralExpr), result);
            var resultAsLiteral = result as LiteralExpr;
            Assert.IsTrue(resultAsLiteral.isBigNum);
            Assert.IsTrue(resultAsLiteral.asBigNum == BigNum.FromInt(3));
        }

        [Test()]
        public void NegativeReals()
        {
            var add = Expr.Add(TestBase.getConstantReal("-1.5"), TestBase.getConstantReal("-2.8"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(add);
            Assert.IsInstanceOfType(typeof(LiteralExpr), result);
            var resultAsLiteral = result as LiteralExpr;
            Assert.IsTrue(resultAsLiteral.isBigDec);
            Assert.AreEqual(BigDec.FromString("-4.3"), resultAsLiteral.asBigDec);
        }

        [Test()]
        public void PositiveReals()
        {
            var add = Expr.Add(TestBase.getConstantReal("1.5"), TestBase.getConstantReal("2.8"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(add);
            Assert.IsInstanceOfType(typeof(LiteralExpr), result);
            var resultAsLiteral = result as LiteralExpr;
            Assert.IsTrue(resultAsLiteral.isBigDec);
            Assert.AreEqual(BigDec.FromString("4.3"), resultAsLiteral.asBigDec);
        }
    }
}

