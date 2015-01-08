using NUnit.Framework;
using Microsoft.Boogie;
using Microsoft.Basetypes;
using Symbooglix;
using System;

namespace ConstantFoldingTests
{
    [TestFixture()]
    public class FoldEq : TestBase
    {
        private void EqualHelper(LiteralExpr constant0, LiteralExpr constant1)
        {
            var TC = new TypecheckingContext(this);
            var equals = Expr.Eq(constant0, constant1);
            equals.Typecheck(TC);
            var CFT = new ConstantFoldingTraverser();


            var result = CFT.Traverse(equals);
            result.Typecheck(TC);
            Assert.IsInstanceOf<LiteralExpr>(result);
            var literal = result as LiteralExpr;
            Assert.IsTrue(literal.isBool);
            Assert.IsTrue(literal.asBool);
        }

        private void NotEqualHelper(LiteralExpr constant0, LiteralExpr constant1)
        {
            var TC = new TypecheckingContext(this);
            var equals = Expr.Eq(constant0, constant1);
            equals.Typecheck(TC);
            var CFT = new ConstantFoldingTraverser();


            var result = CFT.Traverse(equals);
            result.Typecheck(TC);
            Assert.IsInstanceOf<LiteralExpr>(result);
            var literal = result as LiteralExpr;
            Assert.IsTrue(literal.isBool);
            Assert.IsFalse(literal.asBool);
        }

        [Test()]
        public void ConstantBVEqual()
        {
            var constant0 = new LiteralExpr(Token.NoToken, BigNum.FromInt(5), 8); // 5bv8
            var constant1 = new LiteralExpr(Token.NoToken, BigNum.FromInt(5), 8); // 5bv8
            EqualHelper(constant0, constant1);
        }

        [Test()]
        public void ConstantBVNotEqual()
        {
            var constant0 = new LiteralExpr(Token.NoToken, BigNum.FromInt(5), 8); // 5bv8
            var constant1 = new LiteralExpr(Token.NoToken, BigNum.FromInt(12), 8); // 5bv8
            NotEqualHelper(constant0, constant1);
        }

        [Test()]
        public void ConstantBoolEquals()
        {
            var constant0 = new LiteralExpr(Token.NoToken, true);
            var constant1 = new LiteralExpr(Token.NoToken, true);
            EqualHelper(constant0, constant1);
        }

        [Test()]
        public void ConstantBoolNotEquals()
        {
            var constant0 = new LiteralExpr(Token.NoToken, true);
            var constant1 = new LiteralExpr(Token.NoToken, false);
            NotEqualHelper(constant0, constant1);
        }

        [Test()]
        public void ConstantIntEquals()
        {
            var constant0 = getConstantInt(17);
            var constant1 = getConstantInt(17);
            EqualHelper(constant0, constant1);
        }

        [Test()]
        public void ConstantIntNotEquals()
        {
            var constant0 = getConstantInt(17);
            var constant1 = getConstantInt(27);
            NotEqualHelper(constant0, constant1);
        }

        [Test()]
        public void ConstantRealEquals()
        {
            var constant0 = getConstantReal("-79.556");
            var constant1 = getConstantReal("-79.556");
            EqualHelper(constant0, constant1);
        }

        [Test()]
        public void ConstantRealNotEquals()
        {
            var constant0 = getConstantReal("-79.556");
            var constant1 = getConstantReal("-79.557");
            NotEqualHelper(constant0, constant1);
        }

        [Test()]
        public void SymbolicEqual()
        {
            var var0 = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "foo", Microsoft.Boogie.Type.Int));

            // We can't construct a Symbolic variable without a ProgramLocation being attached!
            var0.SetMetadata<ProgramLocation>( (int) Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(var0));

            var sym0 = new SymbolicVariable("sym0", var0);

            var constant = getConstantInt(17);
            var add = Expr.Add(sym0.Expr, constant);
            var TC = new TypecheckingContext(this);
            add.Typecheck(TC);

            // Now duplicate it
            var constant1 = getConstantInt(17);
            var add1 = Expr.Add(sym0.Expr, constant1);
            add1.Typecheck(TC);

            // Now make equals
            var equals = Expr.Eq(add, add1);
            equals.Typecheck(TC);

            // Try folding it
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(equals);
            result.Typecheck(TC);

            Assert.IsInstanceOf<LiteralExpr>(result);
            var literal = result as LiteralExpr;
            Assert.IsTrue(literal.isBool);
            Assert.IsTrue(literal.asBool);
        }

        [Test()]
        public void SymbolicNotEqual()
        {
            var var0 = new GlobalVariable(Token.NoToken, new TypedIdent(Token.NoToken, "foo", Microsoft.Boogie.Type.Int));

            // We can't construct a Symbolic variable without a ProgramLocation being attached!
            var0.SetMetadata<ProgramLocation>( (int) Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(var0));

            var sym0 = new SymbolicVariable("sym0", var0);

            var constant = getConstantInt(17);
            var add = Expr.Add(sym0.Expr, constant);
            var TC = new TypecheckingContext(this);
            add.Typecheck(TC);

            // Now duplicate it
            var constant1 = getConstantInt(19);
            var add1 = Expr.Add(sym0.Expr, constant1);
            add1.Typecheck(TC);

            // Now make equals
            var equals = Expr.Eq(add, add1);
            equals.Typecheck(TC);

            // Try folding it
            var CFT = new ConstantFoldingTraverser();
            var result = CFT.Traverse(equals);
            result.Typecheck(TC);

            Assert.IsNotInstanceOf<LiteralExpr>(result);
            Assert.AreSame(equals, result); // i.e. we didn't do any folding
        }
            


    }
}

