using NUnit.Framework;
using System;
using System.Collections;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldDiv : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void DivideSimpleConstantsInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Div(cfb.ConstantInt(8), cfb.ConstantInt(3));
            Assert.IsInstanceOf<LiteralExpr>(result);
            CheckType(result, p => p.IsInt);
            Assert.AreEqual("2", result.ToString());
        }

        [Test()]
        public void DivideByZero()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Div(cfb.ConstantInt(8), cfb.ConstantInt(0));
            Assert.IsNull(ExprUtil.AsLiteral(result));
            Assert.IsNotNull(ExprUtil.AsDiv(result));
            Assert.AreEqual("8 div 0", result.ToString());
        }

        [Test()]
        public void DivideByOneInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Div(x, cfb.ConstantInt(1));
            Assert.AreSame(x, result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void DivideByOneReal()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var cfb = builderPair.Item2;
            cfb.Div(x, cfb.ConstantReal("1.0"));
        }

        [Test()]
        public void ZeroDivideByIntExpr()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Div(cfb.ConstantInt(0), x);
            Assert.IsFalse(ExprUtil.IsZero(result));
            Assert.IsNotNull(ExprUtil.AsDiv(result));
            CheckIsInt(result);
        }

        [Test(), ExpectedException(typeof(ExprTypeCheckException))]
        public void ZeroDivideByRealExpr()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var cfb = builderPair.Item2;
            cfb.Div(cfb.ConstantReal("0.0"), x);
        }

        [Test()]
        public void NestedDivInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var y = GetVarAndIdExpr("y", BasicType.Int).Item2;
            var z = GetVarAndIdExpr("z", BasicType.Int).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Div(cfb.Div(x, y), z);
            var asDiv = ExprUtil.AsDiv(result);
            Assert.IsNotNull(asDiv);
            CheckIsInt(result);
            Assert.AreSame(x, asDiv.Args[0]);
            var rhsOfDiv = ExprUtil.AsMul(asDiv.Args[1]);
            Assert.IsNotNull(rhsOfDiv);
            Assert.AreSame(y, rhsOfDiv.Args[0]);
            Assert.AreSame(z, rhsOfDiv.Args[1]);

        }

        [Test()]
        public void NoFold()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sfb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var v0 = GetVarAndIdExpr("x", BasicType.Int);
            var v1 = GetVarAndIdExpr("y", BasicType.Int);
            var foldedResult = cfb.Div(v0.Item2, v1.Item2);
            var simpleResult = sfb.Div(v0.Item2, v1.Item2);
            CheckType(foldedResult, p => p.IsInt);
            Assert.AreEqual(simpleResult, foldedResult);
        }
    }
}

