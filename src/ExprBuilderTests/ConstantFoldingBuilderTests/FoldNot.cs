using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldNot : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void simpleTrue()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Not(cfb.True);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsFalse(result));
        }

        [Test()]
        public void simpleFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var result = cfb.Not(cfb.False);
            CheckIsBoolType(result);
            Assert.IsTrue(ExprUtil.IsTrue(result));
        }

        [TestCase(2)]
        [TestCase(3)]
        [TestCase(50)]
        public void nestedNots(int depth)
        {
            var pair = GetVarAndIdExpr("foo", BasicType.Bool);
            var variable = pair.Item1;
            var id = pair.Item2;
            var cfb = GetConstantFoldingBuilder();
            Expr result = id;
            for (int i = 0; i < depth; ++i)
            {
                result = cfb.Not(result);
            }

            if (depth % 2 == 0)
            {
                Assert.AreSame(id, result);
            }
            else
            {
                var asNot = ExprUtil.AsNot(result);
                Assert.IsNotNull(asNot);
                Assert.AreSame(id, asNot.Args[0]);
            }
        }

        [Test()]
        public void noFold()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var result = cfb.Not(id);
            CheckIsBoolType(result);
            var asNot = ExprUtil.AsNot(result);
            Assert.IsNotNull(asNot);
            Assert.AreSame(id, asNot.Args[0]);
        }
    }
}

