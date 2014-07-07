using NUnit.Framework;
using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace BoogieTests
{
    [TestFixture ()]
    public class DuplicatorTests
    {
        Duplicator d;

        [SetUp]
        public void init()
        {
            d = new Duplicator();
        }

        [Test ()]
        public void BVConcatExpr()
        {
            var bv1_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(1), 8);
            var bv2_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(2), 8);
            var A = new BvConcatExpr(Token.NoToken, bv1_8, bv2_8);
            var B = d.Visit(A);

            // The duplicator should ensure we get new BVConcatExprs
            Assert.IsFalse(Object.ReferenceEquals(A, B));
        }

        [Test()]
        public void BvExtractExpr()
        {
            var bv2_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(2), 8);
            var A = new BvExtractExpr(Token.NoToken, bv2_8, 6,0);
            var B = d.Visit(A);

            // The duplicator should ensure we get new BVExtractExprs
            Assert.IsFalse(Object.ReferenceEquals(A, B));
        }

        [Test()]
        public void NaryExpr()
        {
            var bv1_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(1), 8);
            var bv2_8 = new LiteralExpr(Token.NoToken, BigNum.FromInt(2), 8);
            var A = NAryExpr.Eq (bv1_8, bv2_8);
            var B = d.Visit(A);

            Assert.IsFalse(Object.ReferenceEquals(A, B));
        }
    }
}

