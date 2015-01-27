using NUnit.Framework;
using System;
using System.Collections;
using Symbooglix;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class ConstantFoldingExprBuilderTests : SimpleExprBuilderTestBase
    {
        private Tuple<IExprBuilder, IExprBuilder> GetSimpleAndConstantFoldingBuilder()
        {
            var simpleBuilder = GetBuilder();
            var constantFoldingBuilder = new ConstantFoldingExprBuilder(simpleBuilder);
            return new Tuple<IExprBuilder, IExprBuilder>(simpleBuilder, constantFoldingBuilder);
        }

        [Test()]
        public void AddSimpleConstantsInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Add(cfb.ConstantInt(5), cfb.ConstantInt(3));
            Assert.IsInstanceOf<LiteralExpr>(result);
            CheckType(result, p => p.IsInt);
            Assert.AreEqual("8", result.ToString());
        }

        [Test()]
        public void AddZeroToExprInt()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Add(x, cfb.ConstantInt(0));
            Assert.AreEqual("x", result.ToString());
            Assert.IsInstanceOf<IdentifierExpr>(result);
            CheckType(result, p => p.IsInt);
            Assert.AreSame(x, result);
        }

        [Test()]
        public void AddZeroToExprReal()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var cfb = builderPair.Item2;
            var result = cfb.Add(x, cfb.ConstantReal("0.0"));
            Assert.AreEqual("x", result.ToString());
            Assert.IsInstanceOf<IdentifierExpr>(result);
            CheckType(result, p => p.IsReal);
            Assert.AreSame(x, result);
        }

        [Test()]
        public void AddSimpleConstantsReal()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var cfb = builderPair.Item2;
            var result = cfb.Add(cfb.ConstantReal("5.0"), cfb.ConstantReal("3.0"));
            Assert.IsInstanceOf<LiteralExpr>(result);
            CheckType(result, p => p.IsReal);
            Assert.AreEqual("8e0", result.ToString());
        }

        [Test()]
        public void AddSimpleConstantsIntVars()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;
            var result = cfb.Add(x, x);
            CheckType(result, p => p.IsInt);
            Assert.IsInstanceOf<NAryExpr>(result);
            var foldedTopAsNAry = result as NAryExpr;
            Assert.IsInstanceOf<BinaryOperator>(foldedTopAsNAry.Fun);
            Assert.AreEqual(BinaryOperator.Opcode.Mul, (foldedTopAsNAry.Fun as BinaryOperator).Op);
            Assert.IsInstanceOf<LiteralExpr>(foldedTopAsNAry.Args[0]);
            Assert.AreSame(x, foldedTopAsNAry.Args[1]);
            Assert.AreEqual("2 * x", result.ToString());
        }

        [Test()]
        public void AddSimpleConstantsRealVars()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;
            var x = GetVarAndIdExpr("x", BasicType.Real).Item2;
            var result = cfb.Add(x, x);
            CheckType(result, p => p.IsReal);
            Assert.IsInstanceOf<NAryExpr>(result);
            var foldedTopAsNAry = result as NAryExpr;
            Assert.IsInstanceOf<BinaryOperator>(foldedTopAsNAry.Fun);
            Assert.AreEqual(BinaryOperator.Opcode.Mul, (foldedTopAsNAry.Fun as BinaryOperator).Op);
            Assert.IsInstanceOf<LiteralExpr>(foldedTopAsNAry.Args[0]);
            Assert.AreSame(x, foldedTopAsNAry.Args[1]);
            Assert.AreEqual("2e0 * x", result.ToString());
        }

        [Test()]
        public void AddAssociativityPropagateConstantUp()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            Expr foldedResult = sb.ConstantInt(1);
            Expr unfoldedResult = foldedResult;

            for (int index = 0; index < 3; ++index)
            {
                var x = GetVarAndIdExpr("x" + index.ToString(), BasicType.Int).Item2;
                foldedResult = cfb.Add(x, foldedResult);
                unfoldedResult = sb.Add(x, unfoldedResult);
            }
            Assert.AreEqual("1 + x2 + x1 + x0", foldedResult.ToString());
            Assert.AreEqual("x2 + x1 + x0 + 1", unfoldedResult.ToString());
            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            Assert.IsInstanceOf<NAryExpr>(foldedResult);
            var foldedTopAsNAry = foldedResult as NAryExpr;
            Assert.IsInstanceOf<BinaryOperator>(foldedTopAsNAry.Fun);
            Assert.AreEqual(BinaryOperator.Opcode.Add, (foldedTopAsNAry.Fun as BinaryOperator).Op);
            // Check the constant is the top left argument
            Assert.IsInstanceOf<LiteralExpr>(foldedTopAsNAry.Args[0]);
        }

        [Test()]
        public void AddAssociativityAddNearbyConstants()
        {
            var builderPair = GetSimpleAndConstantFoldingBuilder();
            var sb = builderPair.Item1;
            var cfb = builderPair.Item2;

            var x = GetVarAndIdExpr("x", BasicType.Int).Item2;

            Expr foldedResult = x;
            Expr unfoldedResult = foldedResult;

            for (int index = 1; index <= 3; ++index)
            {
                foldedResult = cfb.Add(cfb.ConstantInt(index), foldedResult);
                unfoldedResult = sb.Add(sb.ConstantInt(index), unfoldedResult);
            }
            Assert.AreEqual("6 + x", foldedResult.ToString());
            Assert.AreEqual("3 + 2 + 1 + x", unfoldedResult.ToString());
            Assert.IsFalse(foldedResult.Equals(unfoldedResult));

            Assert.IsInstanceOf<NAryExpr>(foldedResult);
            var foldedTopAsNAry = foldedResult as NAryExpr;
            Assert.IsInstanceOf<BinaryOperator>(foldedTopAsNAry.Fun);
            Assert.AreEqual(BinaryOperator.Opcode.Add, (foldedTopAsNAry.Fun as BinaryOperator).Op);
            // Check the constant is the top left argument
            Assert.IsInstanceOf<LiteralExpr>(foldedTopAsNAry.Args[0]);
        }

    }
}

