using NUnit.Framework;
using Microsoft.Boogie;
using System;
using Symbooglix;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldMul : TestBase
    {
        [Test()]
        public void ConstantInts()
        {
            var arg0 = getConstantInt(5);
            var arg1 = getConstantInt(2);

            var mul = Expr.Mul(arg0, arg1);
            var CFT = new ConstantFoldingTraverser();

            var result = CFT.Traverse(mul);
            Assert.IsInstanceOf<LiteralExpr>(result);
            var literal = result as LiteralExpr;
            Assert.IsTrue(literal.isBigNum);
            Assert.IsTrue(literal.asBigNum.ToBigInteger == 10);
        }

        [Test()]
        public void ConstantReals()
        {
            var arg0 = getConstantReal("5.0");
            var arg1 = getConstantReal("1.5");

            var mul = Expr.Mul(arg0, arg1);
            var CFT = new ConstantFoldingTraverser();

            var result = CFT.Traverse(mul);
            Assert.IsInstanceOf<LiteralExpr>(result);
            var literal = result as LiteralExpr;
            Assert.IsTrue(literal.isBigDec);
            Assert.AreEqual("7.5", literal.asBigDec.ToDecimalString());
        }
    }
}

