using NUnit.Framework;
using System;
using symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class FoldBvConcatExpr : ConstantFoldingTest
    {
        private BvConcatExpr ConcatFactory(int leftValue, int leftWidth, int rightValue, int rightWidth)
        {
            var leftbv = new LiteralExpr(Token.NoToken, BigNum.FromInt(leftValue), leftWidth);
            var rightbv = new LiteralExpr(Token.NoToken, BigNum.FromInt(rightValue), rightWidth);
            var concat = new BvConcatExpr(Token.NoToken, leftbv, rightbv); // {left}bv4 ++ {right}bv4
            Assert.IsTrue(leftbv.Type.IsBv);
            Assert.IsTrue(rightbv.Type.IsBv);

            concat.Typecheck(new TypecheckingContext(this)); // Needed so the type is set.
            Assert.IsTrue(concat.Type.IsBv);
            Assert.AreEqual(concat.Type.BvBits, ( leftbv.Val as BvConst ).Bits + ( rightbv.Val as BvConst ).Bits);
            return concat;
        }

        [Test()]
        public void Simple()
        {
            const int leftValue = 11;
            const int rightValue = 15;
            const int width = 4;
            var concat = ConcatFactory(leftValue, width, rightValue, width);

            var CFT = new ConstantFoldingTraverser();
            Expr replacement = CFT.Traverse(concat);
            Assert.IsTrue(replacement is LiteralExpr);
            var r = replacement as LiteralExpr;
            Assert.IsTrue(r.isBvConst);
            var rBV = r.asBvConst;
            Assert.IsTrue(rBV.Value == BigNum.FromInt(( leftValue << width ) + rightValue));
        }

        [Test()]
        public void TwoLayers()
        {
            const int leftValue = 11;
            const int rightValue = 15;
            const int width = 4;
            var concat = ConcatFactory(leftValue, width, rightValue, width);
            var concat2 = ConcatFactory(leftValue, width, rightValue, width);

            var combined = new BvConcatExpr(Token.NoToken, concat, concat2);
            var CFT = new ConstantFoldingTraverser();
            Expr replacement = CFT.Traverse(combined);
            Assert.IsTrue(replacement is LiteralExpr);
            var r = replacement as LiteralExpr;
            var rBV = r.asBvConst; // FIXME: Boogie's API is lame!
            Assert.AreEqual(rBV.Bits, 16);
            int childValue = ( leftValue << width ) + rightValue;
            int expectedValue = ( childValue << ( width * 2 ) ) + childValue;
            Assert.AreEqual(rBV.Value.ToInt, expectedValue);
        }
    }
}

