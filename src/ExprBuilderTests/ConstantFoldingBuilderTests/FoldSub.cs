using NUnit.Framework;
using System;
using System.Collections;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldSub : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void SubSimpleConstantsInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Sub(cfb.ConstantInt(5), cfb.ConstantInt(3));
            Assert.IsInstanceOf<LiteralExpr>(result);
            CheckType(result, p => p.IsInt);
            Assert.AreEqual("2", result.ToString());
        }

        [Test()]
        public void SubSimpleConstantsReal()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Sub(cfb.ConstantReal("5.0"), cfb.ConstantReal("3.0"));
            Assert.IsInstanceOf<LiteralExpr>(result);
            CheckType(result, p => p.IsReal);
            Assert.AreEqual("2e0", result.ToString());
        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var v1 = GetVarAndIdExpr("y", BasicType.Int);
            var foldedResult = cfb.Sub(v0.Item2, v1.Item2);
            var simpleResult = sfb.Sub(v0.Item2, v1.Item2);
            CheckType(foldedResult, p => p.IsInt);
            Assert.AreEqual(simpleResult, foldedResult);
        }

        // TODO: 0 - <expr> ==> -<expr>
        [Test()]
        public void LhsIntZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var result = cfb.Sub(cfb.ConstantInt(0), x);
            var asNeg = ExprUtil.AsNeg(result);
            Assert.IsNotNull(asNeg);
            Assert.AreSame(x, asNeg.Args[0]);
        }

        // TODO: 0 - <expr> ==> -<expr>
        [Test()]
        public void LhsRealZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var result = cfb.Sub(cfb.ConstantReal("0.0"), x);
            var asNeg = ExprUtil.AsNeg(result);
            Assert.IsNotNull(asNeg);
            Assert.AreSame(x, asNeg.Args[0]);
        }

        // TODO: <expr> - 0 ==> <expr>
        [Test()]
        public void RhsIntZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var result = cfb.Sub(x, cfb.ConstantInt(0));
            Assert.AreSame(x, result);
        }

        [Test()]
        public void RhsRealZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var result = cfb.Sub(x, cfb.ConstantReal("0.0"));
            Assert.AreSame(x, result);
        }

        // <expr> - <constant>  ==> (-<constant>) + <expr>
        [Test()]
        public void MinusConstantIntToAdd()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var constant = cfb.ConstantInt(2);
            var result = cfb.Sub(x, constant);
            var asAdd = ExprUtil.AsAdd(result);
            Assert.IsNotNull(asAdd);
            var lhs = ExprUtil.AsLiteral(asAdd.Args[0]);
            Assert.IsNotNull(lhs);
            Assert.AreEqual(-2, lhs.asBigNum.ToInt);
        }

        // <expr> - <constant>  ==> (-<constant>) + <expr>
        [Test()]
        public void MinusConstantRealToAdd()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var constant = cfb.ConstantReal("2.0");
            var result = cfb.Sub(x, constant);
            var asAdd = ExprUtil.AsAdd(result);
            Assert.IsNotNull(asAdd);
            var lhs = ExprUtil.AsLiteral(asAdd.Args[0]);
            Assert.IsNotNull(lhs);
            Assert.AreEqual("-2e0", lhs.asBigDec.ToString());
        }
 
        // <expr> - <expr> ==> 0
        [Test()]
        public void SubtractIdenticalIntExpr()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var y = GetVarAndIdExpr("y", BasicType.Int).Item2;
            var side = cfb.Add(x, y);
            var result = cfb.Sub(side, side);
            var asLit = ExprUtil.AsLiteral(result);
            CheckIsInt(result);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(asLit.asBigNum.IsZero);
        }

        [Test()]
        public void SubtractIdenticalRealExpr()
        {
            var cfb = GetConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var y = GetVarAndIdExpr("y", BasicType.Real).Item2;
            var side = cfb.Add(x, y);
            var result = cfb.Sub(side, side);
            var asLit = ExprUtil.AsLiteral(result);
            CheckIsReal(result);
            Assert.IsNotNull(asLit);
            Assert.IsTrue(asLit.asBigDec.IsZero);
        }
    }
}

