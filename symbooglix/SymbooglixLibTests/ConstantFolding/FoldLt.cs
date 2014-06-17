using NUnit.Framework;
using System;
using Microsoft.Boogie;
using symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class FoldLt : ConstantFoldingTest
    {
        [Test()]
        public void IntFalse()
        {
            var lt = Expr.Lt( getConstantInt(0), getConstantInt(-1));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(lt);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.False);
        }

        [Test()]
        public void IntTrue()
        {
            var lt = Expr.Lt( getConstantInt(-2), getConstantInt(-1));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(lt);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.True);
        }

        [Test()]
        public void IntEquals()
        {
            var lt = Expr.Lt( getConstantInt(-1), getConstantInt(-1));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(lt);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.False);
        }

        [Test()]
        public void RealFalse()
        {
            var lt = Expr.Lt( getConstantReal("0.5"), getConstantReal("0.2"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(lt);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.False);
        }

        [Test()]
        public void RealTrue()
        {
            var lt = Expr.Lt( getConstantReal("0.5"), getConstantReal("0.75"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(lt);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.True);
        }

        [Test()]
        public void RealEquals()
        {
            var lt = Expr.Lt( getConstantReal("0.5"), getConstantReal("0.5"));
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(lt);
            Assert.IsTrue(result is LiteralExpr);
            Assert.AreSame(result, Expr.False);
        }
    }
}

