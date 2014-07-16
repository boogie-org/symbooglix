using NUnit.Framework;
using Microsoft.Boogie;
using Symbooglix;
using System;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldNeg : TestBase
    {
        // FIXME: This belongs in Boogie
        public static Expr GetNeg(Expr v)
        {
            return Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Neg, v);
        }

        [Test()]
        public void Integer()
        {
            var negation = GetNeg(getConstantInt(1));
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
            var negation = GetNeg(GetNeg(getConstantInt(1)));
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
            var negation = GetNeg(getConstantReal("2.0"));
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
            var negation = GetNeg(GetNeg(getConstantReal("2.0")));
            var CFT = new ConstantFoldingTraverser();
            var e = CFT.Traverse(negation);

            Assert.IsInstanceOfType(typeof(LiteralExpr), e);
            var literal = e as LiteralExpr;
            Assert.IsTrue(literal.isBigDec);
            Assert.AreEqual(literal.asBigDec.ToString(), "2e0");
        }
    }
}

