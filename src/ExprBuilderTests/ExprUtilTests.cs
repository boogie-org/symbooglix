using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class ExprUtilTests : SimpleExprBuilderTestBase
    {
        [Test()]
        public void AsLiteralWithLiteral()
        {
            var sb = GetSimpleBuilder();
            var lit = sb.True;
            Assert.IsInstanceOf<LiteralExpr>(lit);
            var asLit = ExprUtil.AsLiteral(lit);
            Assert.IsNotNull(asLit);
            Assert.AreSame(lit, asLit);
        }

        [Test()]
        public void AsLiteralWithNonLiteral()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var e = sb.Eq(v, sb.False);
            Assert.IsNotInstanceOf<LiteralExpr>(e);
            var asLit = ExprUtil.AsLiteral(e);
            Assert.IsNull(asLit);
        }

        [Test()]
        public void IsTrueWithTrue()
        {
            var sb = GetSimpleBuilder();
            var e = sb.True;
            Assert.IsTrue(ExprUtil.IsTrue(e));
        }

        [Test()]
        public void IsTrueWithFalse()
        {
            var sb = GetSimpleBuilder();
            var e = sb.False;
            Assert.IsFalse(ExprUtil.IsTrue(e));
        }

        [Test()]
        public void IsTrueWithWithExpr()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var e = sb.Eq(v, sb.False);
            Assert.IsFalse(ExprUtil.IsTrue(e));
        }

        [Test()]
        public void IsFalseWithTrue()
        {
            var sb = GetSimpleBuilder();
            var e = sb.True;
            Assert.IsFalse(ExprUtil.IsFalse(e));
        }

        [Test()]
        public void IsFalseWithFalse()
        {
            var sb = GetSimpleBuilder();
            var e = sb.False;
            Assert.IsTrue(ExprUtil.IsFalse(e));
        }

        [Test()]
        public void IsFalseWithWithExpr()
        {
            var sb = GetSimpleBuilder();
            var v = GetVarAndIdExpr("foo", BasicType.Bool).Item2;
            var e = sb.Eq(v, sb.False);
            Assert.IsFalse(ExprUtil.IsFalse(e));
        }
    }
}

