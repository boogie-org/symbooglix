using NUnit.Framework;
using System;
using symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class FoldBvExtractExpr : IErrorSink
    {
        [Test()]
        public void Simple()
        {
            const int left = 11;
            const int right = 15;
            var leftbv4 = new LiteralExpr(Token.NoToken, BigNum.FromInt(left), 4);
            var rightbv4 = new LiteralExpr(Token.NoToken, BigNum.FromInt(right), 4);
            var concat = new BvConcatExpr(Token.NoToken, leftbv4, rightbv4); // {left}bv4 ++ {right}bv4
            Assert.IsTrue(leftbv4.Type.IsBv);
            Assert.IsTrue(rightbv4.Type.IsBv);

            concat.Typecheck(new TypecheckingContext(this)); // Needed so the type is set.
            Assert.IsTrue(concat.Type.IsBv);
            Assert.AreEqual(concat.Type.BvBits, ( leftbv4.Val as BvConst ).Bits + ( rightbv4.Val as BvConst ).Bits);

            var CFT = new ConstantFoldingTraverser();
            Expr replacement = CFT.Traverse(concat);
            Assert.IsTrue(replacement is LiteralExpr);
            var r = replacement as LiteralExpr;
            Assert.IsTrue(r.Type.IsBv);
            var rBV = r.Val as BvConst; // FIXME: Boogie's API is lame!
            Assert.AreEqual(rBV.Bits, 8);
            Assert.IsTrue(rBV.Value == BigNum.FromInt(( left << 4 ) + right));
        }

        public void Error(IToken tok, string msg)
        {
            Assert.Fail(msg);
        }
    }
}

