using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using symbooglix;

// FIXME: Change namespace so constant folding tests are in different namespace.
namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldLe : TestBase
    {
        [Test()]
        public void IntFalse()
        {
            var le = Expr.Le( getConstantInt(0), getConstantInt(-1));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(le);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.False);
        }

        [Test()]
        public void IntTrue()
        {
            var le = Expr.Le( getConstantInt(-2), getConstantInt(-1));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(le);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.True);
        }

        [Test()]
        public void IntEquals()
        {
            var le = Expr.Le( getConstantInt(-1), getConstantInt(-1));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(le);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.True);
        }

        [Test()]
        public void RealFalse()
        {
            var le = Expr.Le( getConstantReal("0.5"), getConstantReal("0.2"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(le);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.False);
        }

        [Test()]
        public void RealTrue()
        {
            var le = Expr.Le( getConstantReal("0.5"), getConstantReal("0.75"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(le);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.True);
        }

        [Test()]
        public void RealEquals()
        {
            var le = Expr.Le( getConstantReal("0.5"), getConstantReal("0.5"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(le);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.True);
        }
    }
}

