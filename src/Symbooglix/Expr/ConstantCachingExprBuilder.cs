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
using Microsoft.Boogie;
using System.Numerics;
using Microsoft.Basetypes;
using System.Diagnostics;
using System.Collections.Generic;

namespace Symbooglix
{
    public class ConstantCachingExprBuilder : DecoratorExprBuilder
    {
        private LiteralExpr CachedTrueExpr;
        private LiteralExpr CachedFalseExpr;
        private Dictionary<BigInteger, LiteralExpr> IntegerCache; // FIXME: Should probably use concurrent dictionary for thread safety
        private Dictionary<BigDec, LiteralExpr> RealCache; // FIXME: Should probably use concurrent dictionary for thread safety
        private Dictionary<int, Dictionary<BigInteger,LiteralExpr>> BitVectorCache; // FIXME: Should probably use concurrent dictionary for thread safety
        public ConstantCachingExprBuilder(IExprBuilder underlyingBuilder) : base(underlyingBuilder)
        {
            // It's not safe to cache expressions if the underlying builder does not give immutable LiteralExprs
            if (!UB.Immutable)
                throw new ArgumentException("Underlying builder must build immutable expressions");

            // Setup Caches
            this.CachedTrueExpr = UB.True;
            Debug.Assert(this.CachedTrueExpr.isBool && this.CachedTrueExpr.asBool);
            this.CachedFalseExpr = UB.False;
            Debug.Assert(this.CachedFalseExpr.isBool && !this.CachedFalseExpr.asBool);
            this.IntegerCache = new Dictionary<BigInteger, LiteralExpr>();
            this.RealCache = new Dictionary<BigDec, LiteralExpr>();
            this.BitVectorCache = new Dictionary<int, Dictionary<BigInteger, LiteralExpr>>();
        }

        public override LiteralExpr True
        {
            get
            {
                return this.ConstantBool(true);
            }
        }

        public override LiteralExpr False
        {
            get
            {
                return this.ConstantBool(false);
            }
        }

        public override LiteralExpr ConstantBool(bool value)
        {
            if (value)
                return CachedTrueExpr;
            else
                return CachedFalseExpr;
        }


        public override LiteralExpr ConstantInt(int value)
        {
            return this.ConstantInt(new BigInteger(value));
        }

        public override LiteralExpr ConstantInt(BigInteger decimalValue)
        {
            try
            {
                var cachedInt = IntegerCache[decimalValue];
                Debug.Assert(cachedInt.isBigNum);
                return cachedInt;
            }
            catch (KeyNotFoundException)
            {
                var newInt = UB.ConstantInt(decimalValue);
                Debug.Assert(newInt.isBigNum);
                IntegerCache.Add(decimalValue, newInt);
                return newInt;
            }
        }

        public override LiteralExpr ConstantReal(string value)
        {
            return this.ConstantReal(BigDec.FromString(value));
        }

        public override LiteralExpr ConstantReal(BigDec value)
        {
            try
            {
                var cachedReal = RealCache[value];
                Debug.Assert(cachedReal.isBigDec);
                return cachedReal;
            }
            catch (KeyNotFoundException)
            {
                var newReal = UB.ConstantReal(value);
                Debug.Assert(newReal.isBigDec);
                RealCache.Add(value, newReal);
                return newReal;
            }
        }


        public override LiteralExpr ConstantBV(int decimalValue, int bitWidth)
        {
            return this.ConstantBV(new BigInteger(decimalValue), bitWidth);
        }

        public override LiteralExpr ConstantBV(BigInteger decimalValue, int bitWidth)
        {
            // Get the right dictionary for the bitwidth
            Dictionary<BigInteger, LiteralExpr> mapping = null;
            try
            {
                mapping = BitVectorCache[bitWidth];
            }
            catch (KeyNotFoundException)
            {
                mapping = new Dictionary<BigInteger, LiteralExpr>();
                BitVectorCache.Add(bitWidth, mapping);
            }

            try
            {
                var constant = mapping[decimalValue];
                Debug.Assert(constant.isBvConst);
                return constant;
            }
            catch (KeyNotFoundException)
            {
                var newBv = UB.ConstantBV(decimalValue, bitWidth);
                Debug.Assert(newBv.isBvConst);
                mapping.Add(decimalValue, newBv);
                return newBv;
            }
        }


    }
}

