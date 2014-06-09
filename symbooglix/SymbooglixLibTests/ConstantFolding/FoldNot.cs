using NUnit.Framework;
using System;
using Microsoft.Boogie;
using symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class FoldNot : ConstantFoldingTest
    {
        [Test()]
        public void NotTrue()
        {
            fold(Expr.Not(Expr.True), Expr.False);
        }

        [Test()]
        public void NotFalse()
        {
            fold(Expr.Not(Expr.False), Expr.True);
        }

        public void fold(Expr original, Expr expected)
        {
            var CFT = new ConstantFoldingTraverser();
            var TC = new TypecheckingContext(this);
            original.Typecheck(TC);
            expected.Typecheck(TC);

            Expr result = CFT.Traverse(original);
            Assert.AreSame(result, expected);
        }
    }
}

