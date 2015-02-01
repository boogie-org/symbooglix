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
            var constantBuilder = GetConstantFoldingBuilder();
            var id0 = GetVarAndIdExpr("foo", BasicType.GetBvType(8)).Item2;
            var id1 = GetVarAndIdExpr("bar", BasicType.GetBvType(8)).Item2;
            var result = constantBuilder.IfThenElse(constantBuilder.True, id0, id1);
            Assert.AreEqual("foo", result.ToString());
            CheckIsBvType(result, 8);
            Assert.AreSame(result, id0);
        }

        [Test()]
        public void IfFalse()
        {
            var cfb = GetConstantFoldingBuilder();
            var id0 = GetVarAndIdExpr("foo", BasicType.GetBvType(8)).Item2;
            var id1 = GetVarAndIdExpr("bar", BasicType.GetBvType(8)).Item2;
            Expr result = cfb.IfThenElse(Expr.False, id0, id1);
            Assert.AreEqual("bar", result.ToString());
            CheckIsBvType(result, 8);
            Assert.AreSame(result, id1);
        }


        [Test()]
        public void IfConditionThenConditionAndElseFalse()
        {
            var builder = GetConstantFoldingBuilder();
            var v = GetVarAndIdExpr("v", BasicType.Bool).Item2;
            var result = builder.IfThenElse(v, v, builder.False);
            Assert.AreEqual("v", result.ToString());
            Assert.AreSame(v, result);
            CheckIsBoolType(result);
        }

        [Test()]
        public void IfNotConditionThenConditionElseTrue()
        {
            var v = GetVarAndIdExpr("v", BasicType.Bool).Item2;
            var builder = GetConstantFoldingBuilder();
            var result = builder.IfThenElse(builder.Not(v), v, builder.True);
            Assert.AreEqual("v", result.ToString());
            Assert.AreSame(v, result);
            CheckIsBoolType(result);
        }

        [Test()]
        public void IfConditionThenTrueElseCondition()
        {
            var builder = GetConstantFoldingBuilder();
            var v = GetVarAndIdExpr("v", BasicType.Bool).Item2;
            var y = GetVarAndIdExpr("y", BasicType.Bool).Item2;
            var vNotEqy = builder.NotEq(v, y);

            var result = builder.IfThenElse(vNotEqy, builder.True, vNotEqy);
            Assert.AreEqual("v != y", result.ToString());
            Assert.AreSame(vNotEqy, result);
            CheckIsBoolType(result);
        }
    }
}

