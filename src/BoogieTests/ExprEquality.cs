using Microsoft.Basetypes;
using Microsoft.Boogie;
using NUnit.Framework;
using System;
using SymbooglixLibTests;

namespace BoogieTests
{
    [TestFixture()]
    public class ExprEquality
    {
        // This was never a bug in Boogie
        [Test()]
        public void LiteralBool()
        {
            var constant = new LiteralExpr(Token.NoToken, false);
            var constant2 = new LiteralExpr(Token.NoToken, false);

            Assert.IsFalse(constant == constant2); // These are different references

            Assert.IsTrue(constant.Equals(constant2)); // These are "structurally equal"
        }

        // This was never a bug in Boogie
        [Test()]
        public void LiteralBV()
        {
            var constant = new LiteralExpr(Token.NoToken, BigNum.FromInt(5), 8); // 5bv8;
            var constant2 = new LiteralExpr(Token.NoToken, BigNum.FromInt(5), 8); // 5bv8;

            Assert.IsFalse(constant == constant2); // These are different references

            Assert.IsTrue(constant.Equals(constant2)); // These are "structurally equal"
        }

        // This was never a bug in Boogie
        [Test()]
        public void LiteralInt()
        {
            var constant = ConstantFoldingTests.TestBase.getConstantInt(18);
            var constant2 = ConstantFoldingTests.TestBase.getConstantInt(18);

            Assert.IsFalse(constant == constant2); // These are different references

            Assert.IsTrue(constant.Equals(constant2)); // These are "structurally equal"
        }

        // This was never a bug in Boogie
        [Test()]
        public void LiteralReal()
        {
            var constant = ConstantFoldingTests.TestBase.getConstantReal("11.7");
            var constant2 = ConstantFoldingTests.TestBase.getConstantReal("11.7");

            Assert.IsFalse(constant == constant2); // These are different references

            Assert.IsTrue(constant.Equals(constant2)); // These are "structurally equal"
        }

        // This was a bug in Boogie
        [Test()]
        public void simpleAdd()
        {
            var constant = ConstantFoldingTests.TestBase.getConstantInt(18);
            var constant2 = ConstantFoldingTests.TestBase.getConstantInt(19);
            var add = Expr.Add(constant, constant2);

            var add2 = Expr.Add(constant, constant2);

            Assert.IsFalse(add == add2); // These are different references

            Assert.IsTrue(add.Equals(add2)); // These are "structurally equal"
        }
    }
}

