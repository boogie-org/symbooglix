using NUnit.Framework;
using System;
using Symbooglix;
using Microsoft.Boogie;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBvsmod : TestBase
    {
        [Test()]
        public void PositiveNumeratorPositiveDenominatorWithRemainder()
        {
            var arg0 = builder.ConstantBV(7, 4);
            var arg1 = builder.ConstantBV(2, 4);
            helper(arg0, arg1, 1);
        }

        [Test()]
        public void PositiveNumeratorPositiveDenominatorNoRemainder()
        {
            var arg0 = builder.ConstantBV(8, 4);
            var arg1 = builder.ConstantBV(2, 4);
            helper(arg0, arg1, 0);
        }

        [Test()]
        public void PositiveNumeratorNegativeDenominatorWithRemainder()
        {
            var arg0 = builder.ConstantBV(7, 4);
            var arg1 = builder.ConstantBV(-2, 4);
            helper(arg0, arg1, -1);
        }

        [Test()]
        public void PositiveNumeratorNegativeDenominatorNoRemainder()
        {
            var arg0 = builder.ConstantBV(8, 4);
            var arg1 = builder.ConstantBV(-2, 4);
            helper(arg0, arg1, 0);
        }

        [Test()]
        public void NegativeNumeratorPositiveDenominatorWithRemainder()
        {
            var arg0 = builder.ConstantBV(-7, 4);
            var arg1 = builder.ConstantBV(2, 4);
            helper(arg0, arg1, 1);
        }

        [Test()]
        public void NegativeNumeratorNegativeDenominatorWithRemainder()
        {
            /*
            (declare-fun a () (_ BitVec 4))
            (declare-fun b () (_ BitVec 4))
            (declare-fun c () (_ BitVec 4))
            (assert (= a #b1001))
            (assert (= b #b1110))
            (assert (= c(bvsmod a b)))
            (check-sat)
            (get-model)
            */

            var arg0 = builder.ConstantBV(-7, 4);
            var arg1 = builder.ConstantBV(-2, 4);
            helper(arg0, arg1, -1);
        }

        [Test()]
        public void DivisionByZero()
        {
            var arg0 = builder.ConstantBV(-7, 4);
            var arg1 = builder.ConstantBV(0, 4);
            var smod = builder.BVSMOD(arg0, arg1);
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(smod);
            Assert.IsNotInstanceOf<LiteralExpr>(result);
            Assert.AreSame(result, smod);

        }

        private Expr helper(Expr arg0, Expr arg1, int expected)
        {
            var smod = builder.BVSMOD(arg0, arg1);

            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(smod);
            Assert.IsInstanceOf<LiteralExpr>(result);
            Assert.IsTrue(( result as LiteralExpr ).isBvConst);
            Assert.AreEqual(builder.ConstantBV(expected, 4).asBvConst.Value, ( result as LiteralExpr ).asBvConst.Value);
            return result;
        }
    }
}

