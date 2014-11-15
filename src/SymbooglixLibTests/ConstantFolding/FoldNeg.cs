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

            Assert.IsInstanceOf<LiteralExpr>(e);
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

            Assert.IsInstanceOf<LiteralExpr>(e);
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

            Assert.IsInstanceOf<LiteralExpr>(e);
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

            Assert.IsInstanceOf<LiteralExpr>(e);
            var literal = e as LiteralExpr;
            Assert.IsTrue(literal.isBigDec);
            Assert.AreEqual(literal.asBigDec.ToString(), "2e0");
        }

        [Test()]
        public void GPUVerifyLiteralAssignment()
        {
            // Check (if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1;
            // is folded to
            // group_size_y == 1bv32
            var variable = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "group_size_y", Microsoft.Boogie.Type.GetBvType(32)));
            var onebv32 = builder.ConstantBV(1, 32);
            var trueBv = builder.ConstantBV(1, 1);
            var falseBv = builder.ConstantBV(0, 1);
            var expectedResult = builder.Eq( new IdentifierExpr(Token.NoToken, variable), onebv32);

            var initial = builder.NotEq( builder.IfThenElse(expectedResult, trueBv, falseBv), falseBv);
            Assert.AreEqual("(if group_size_y == 1bv32 then 1bv1 else 0bv1) != 0bv1", initial.ToString());

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(initial);
            Assert.AreEqual("group_size_y == 1bv32", result.ToString());
            Assert.IsTrue(result.Equals(expectedResult));
        }

        // I've not seen this in practise but it was easy to catch this constant folding opportunity
        [Test()]
        public void VariantOfGPUVerifyLiteralAssignment()
        {
            // Check (if group_size_y == 1bv32 then 0bv1 else 1bv1) != 0bv1;
            // is folded to
            // !(group_size_y == 1bv32)
            var variable = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "group_size_y", Microsoft.Boogie.Type.GetBvType(32)));
            var onebv32 = builder.ConstantBV(1, 32);
            var trueBv = builder.ConstantBV(1, 1);
            var falseBv = builder.ConstantBV(0, 1);
            var conditionExpr = builder.Eq( new IdentifierExpr(Token.NoToken, variable), onebv32);

            var initial = builder.NotEq( builder.IfThenElse(conditionExpr, falseBv, trueBv), falseBv);
            Assert.AreEqual("(if group_size_y == 1bv32 then 0bv1 else 1bv1) != 0bv1", initial.ToString());

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(initial);
            Assert.AreEqual("!(group_size_y == 1bv32)", result.ToString());
            Assert.IsTrue(result.Equals( builder.Not(conditionExpr) ));
        }
    }
}

