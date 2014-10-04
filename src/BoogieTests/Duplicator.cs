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

        [Test()]
        public void WholeProgram()
        {
            var p = new Program();
            var t = new TypedIdent(Token.NoToken, "foo", Microsoft.Boogie.Type.Bool);
            var gv = new GlobalVariable(Token.NoToken, t);
            p.AddTopLevelDeclaration(gv);

            // Now try to clone
            var p2 = (Program) d.Visit(p);

            // Check global is a copy
            int counter = 0;
            GlobalVariable gv2 = null;
            foreach (var g in p2.TopLevelDeclarations)
            {
                ++counter;
                Assert.IsInstanceOfType(typeof(GlobalVariable), g);
                gv2 = g as GlobalVariable;
            }
            Assert.AreEqual(1, counter);
            Assert.AreNotSame(gv, gv2);

            // Check Top level declarations list is duplicated properly
            var t2 = new TypedIdent(Token.NoToken, "bar", Microsoft.Boogie.Type.Bool);
            var gv3 = new GlobalVariable(Token.NoToken, t2);
            p2.AddTopLevelDeclaration(gv3);

            counter = 0;
            foreach (var g in p2.TopLevelDeclarations)
            {
                ++counter;
                Assert.IsInstanceOfType(typeof(GlobalVariable), g);
            }
            Assert.AreEqual(2, counter);

            // The original program should still only have one global variable
            counter = 0;
            foreach (var g in p.TopLevelDeclarations)
            {
                ++counter;
                Assert.IsInstanceOfType(typeof(GlobalVariable), g);
            }

            // FIXME: This currently fails in Boogie
            Assert.AreEqual(1, counter);
        }
    }
}

