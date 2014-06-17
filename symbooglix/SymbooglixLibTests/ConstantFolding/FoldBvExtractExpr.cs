using NUnit.Framework;
using Microsoft.Basetypes;
using Microsoft.Boogie;
using symbooglix;
using System;


namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBvExtractExpr : TestBase
    {
        [Test()]
        public void simple()
        {
            var bv = new LiteralExpr(Token.NoToken, BigNum.FromInt(165), 8); // 0b10100101
            var extractExpr = new BvExtractExpr(Token.NoToken, bv, 5, 1); // should be 0b0010
            var tc = new TypecheckingContext(this);
            extractExpr.Typecheck(tc);

            Assert.IsTrue(extractExpr.Type.IsBv);
            Assert.AreEqual(extractExpr.Type.BvBits, 4);

            var CFT = new ConstantFoldingTraverser();
            Expr replacement = CFT.Traverse(extractExpr);

            Assert.IsInstanceOfType(typeof(LiteralExpr), replacement);
            var replacementAsLiteralExpr = replacement as LiteralExpr;
            Assert.IsTrue(replacementAsLiteralExpr.isBvConst);
            var resultBv = replacementAsLiteralExpr.asBvConst;
            Assert.AreEqual(resultBv.Bits, 4);
            Assert.AreEqual(resultBv.Value.ToInt, 2);
        }
    }
}

