using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using symbooglix;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldGe : ConstantFoldingTest
    {
        [Test()]
        public void IntFalse()
        {
            var ge = Expr.Ge( getConstantInt(-2), getConstantInt(-1));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(ge);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.False);
        }

        [Test()]
        public void IntTrue()
        {
            var ge = Expr.Ge( getConstantInt(2), getConstantInt(-1));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(ge);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.True);
        }

        [Test()]
        public void IntEquals()
        {
            var ge = Expr.Ge( getConstantInt(-1), getConstantInt(-1));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(ge);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.True);
        }

        [Test()]
        public void RealFalse()
        {
            var le = Expr.Ge( getConstantReal("0.1"), getConstantReal("0.2"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(le);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.False);
        }

        [Test()]
        public void RealTrue()
        {
            var ge = Expr.Ge( getConstantReal("0.5"), getConstantReal("0.25"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(ge);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.True);
        }

        [Test()]
        public void RealEquals()
        {
            var ge = Expr.Ge( getConstantReal("0.5"), getConstantReal("0.5"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(ge);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.True);
        }
    }
}

