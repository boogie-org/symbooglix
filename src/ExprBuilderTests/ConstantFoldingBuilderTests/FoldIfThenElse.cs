using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;

namespace ExprBuilderTests
{
    public class FoldIfThenElse : ConstantFoldingExprBuilderTests
    {
        [Test()]
        public void IfTrue()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var constantBuilder = builderPair.Item2;
            var simpleBuilder = builderPair.Item1;
            var id0 = GetVarAndIdExpr("foo", BasicType.GetBvType(8)).Item2;
            var id1 = GetVarAndIdExpr("bar", BasicType.GetBvType(8)).Item2;
            var result = constantBuilder.IfThenElse(constantBuilder.True, id0, id1);
            CheckIsBvType(result, 8);
            Assert.AreSame(result, id0);
        }

        [Test()]
        public void IfFalse()
        {
            var cfb = GetSimpleAndConstantFoldingBuilder().Item2;
            var id0 = GetVarAndIdExpr("foo", BasicType.GetBvType(8)).Item2;
            var id1 = GetVarAndIdExpr("bar", BasicType.GetBvType(8)).Item2;
            Expr result = cfb.IfThenElse(Expr.False, id0, id1);
            CheckIsBvType(result, 8);
            Assert.AreSame(result, id1);
        }


        [Test()]
        public void IfConditionThenConditionAndElseFalse()
        {
            var builder = GetSimpleAndConstantFoldingBuilder().Item2;
            var v = GetVarAndIdExpr("v", BasicType.Bool).Item2;
            var result = builder.IfThenElse(v, v, builder.False);
            Assert.AreSame(v, result);
            CheckIsBoolType(result);
        }

        [Test()]
        public void IfNotConditionThenConditionElseTrue()
        {
            var v = GetVarAndIdExpr("v", BasicType.Bool).Item2;
            var builder = GetSimpleAndConstantFoldingBuilder().Item2;
            var result = builder.IfThenElse(builder.Not(v), v, builder.ConstantBool(true));
            Assert.AreSame(v, result);
            CheckIsBoolType(result);
        }

        [Test()]
        public void IfConditionThenTrueElseCondition()
        {
            var builder = GetSimpleAndConstantFoldingBuilder().Item2;
            var v = GetVarAndIdExpr("v", BasicType.Bool).Item2;
            var y = GetVarAndIdExpr("y", BasicType.Bool).Item2;
            var vNotEqy = builder.NotEq(v, y);

            var result = builder.IfThenElse(vNotEqy, builder.ConstantBool(true), vNotEqy);
            Assert.AreSame(vNotEqy, result);
            CheckIsBoolType(result);
        }
    }
}

