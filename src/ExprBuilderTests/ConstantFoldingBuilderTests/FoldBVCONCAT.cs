//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;
using System.Numerics;

namespace ExprBuilderTests.ConstantFoldingTests
{
    [TestFixture()]
    public class FoldBVCONCAT : ConstantFoldingExprBuilderTests
    {
        // Brute force
        [TestCase(8, 8)]
        public void simpleConstants(int msbMaxBitWidth, int lsbMaxBitWidth)
        {
            var cfb = GetConstantFoldingBuilder();
            for (int msbBitWidth=1; msbBitWidth <= msbMaxBitWidth ; ++msbBitWidth)
            {
                int msbMaxValue = (1 << msbBitWidth) -1;
                for (int lsbBitWidth=1; lsbBitWidth <= lsbMaxBitWidth; ++lsbBitWidth)
                {
                    int lsbMaxValue = (1 << lsbBitWidth) -1;
                    for (int msbValue = 0; msbValue <= msbMaxValue; ++msbValue)
                    {
                        Expr msbExpr = cfb.ConstantBV(msbValue, msbBitWidth);
                        for (int lsbValue = 0; lsbValue <= lsbMaxValue; ++lsbValue)
                        {
                            Expr lsbExpr = cfb.ConstantBV(lsbValue, lsbBitWidth);
                            var result = cfb.BVCONCAT(msbExpr, lsbExpr);
                            var expectedWidth = msbBitWidth + lsbBitWidth;
                            CheckIsBvType(result, expectedWidth);
                            var asLit = ExprUtil.AsLiteral(result);


                            var expectedValueInDecimalRepr = ((new BigInteger(msbValue)) << lsbBitWidth) + (new BigInteger(lsbValue));
                            Assert.IsNotNull(asLit);
                            Assert.AreEqual(expectedValueInDecimalRepr, asLit.asBvConst.Value.ToBigInteger);
                        }
                    }
                }
            }
        }

        [Test()]
        public void MSBIsZero()
        {
            var cfb = GetConstantFoldingBuilder();
            var msb = cfb.ConstantBV(0, 8);
            var lsb = GetVarAndIdExpr("x", BasicType.GetBvType(4)).Item2;
            var result = cfb.BVCONCAT(msb, lsb);

            var asBvZExt = ExprUtil.AsBVZEXT(result);
            Assert.IsNotNull(asBvZExt);
            CheckIsBvType(result, 12);
            Assert.AreSame(lsb, asBvZExt.Args[0]);
        }

        [Test()]
        public void noFold()
        {
            var pair = GetSimpleAndConstantFoldingBuilder();
            var sb = pair.Item1;
            var cfb = pair.Item2;
            var id0 = GetVarAndIdExpr("foo0", BasicType.GetBvType(8)).Item2;
            var id1 = GetVarAndIdExpr("foo1", BasicType.GetBvType(8)).Item2;
            var foldedResult = cfb.BVCONCAT(id0, id1);
            var simpleResult = sb.BVCONCAT(id0, id1);

            // FIXME: Typechecking a BvConcatExpr is broken in Boogie, it tries to change the type!
            //CheckIsBvType(foldedResult, 16);
            Assert.IsTrue(foldedResult.Type.IsBv);
            Assert.AreEqual(16, foldedResult.Type.BvBits);

            Assert.AreEqual(simpleResult, foldedResult);

            var asBvConcat = ExprUtil.AsBVCONCAT(foldedResult);
            Assert.IsNotNull(asBvConcat);
            Assert.AreSame(id0, asBvConcat.E0);
            Assert.AreSame(id1, asBvConcat.E1);
        }

        [Test()]
        public void ConcatExtractsToOriginal()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(16)).Item2;
            var msb = cfb.BVEXTRACT(id, 16, 8);
            var lsb = cfb.BVEXTRACT(id, 8, 0);
            var result = cfb.BVCONCAT(msb, lsb);
            CheckIsBvType(result, 16);
            Assert.AreSame(id, result);
        }

        [Test()]
        public void ConcatExtractsToSingleExtract()
        {
            var cfb = GetConstantFoldingBuilder();
            var id = GetVarAndIdExpr("x", BasicType.GetBvType(16)).Item2;
            var msb = cfb.BVEXTRACT(id, 16, 8);
            var lsb = cfb.BVEXTRACT(id, 8, 5);
            var result = cfb.BVCONCAT(msb, lsb);
            CheckIsBvType(result, 11);
            var asBvExtract = ExprUtil.AsBVEXTRACT(result);
            Assert.IsNotNull(asBvExtract);
            Assert.AreSame(id, asBvExtract.Bitvector);
            Assert.AreEqual(16, asBvExtract.End);
            Assert.AreEqual(5, asBvExtract.Start);
        }

        [Test()]
        public void ConcatExtractsNoFold()
        {
            var cfb = GetConstantFoldingBuilder();
            var id0 = GetVarAndIdExpr("x", BasicType.GetBvType(16)).Item2;
            var id1 = GetVarAndIdExpr("y", BasicType.GetBvType(16)).Item2;
            var msb = cfb.BVEXTRACT(id0, 16, 8);
            var lsb = cfb.BVEXTRACT(id1, 8, 0);

            // Different variables so this should not be simplified to a single extract
            var result = cfb.BVCONCAT(msb, lsb);

            // FIXME: Can't check type due to bugs in Boogie. It tries to change the type on immutabl Expr
            // CheckIsBvType(result, 16);
            Assert.IsTrue(result.Type.IsBv);
            Assert.AreEqual(16, result.Type.BvBits);

            var asBvConcat = ExprUtil.AsBVCONCAT(result);
            Assert.IsNotNull(asBvConcat);
            Assert.AreSame(msb, asBvConcat.E0);
            Assert.AreSame(lsb, asBvConcat.E1);
        }
    }
}

