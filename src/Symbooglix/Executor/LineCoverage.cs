//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2017 Daniel Liew
//
// This file is licensed under the MIT license.
// See LICENSE.txt for details.
//------------------------------------------------------------------------------
using System;

namespace Symbooglix
{
    public struct LineCoverage
    {
        public int CoveredLines;
        public int TotalLines;

        public static LineCoverage operator+(LineCoverage lhs, LineCoverage rhs)
        {
            var that = new LineCoverage();
            that.CoveredLines = lhs.CoveredLines + rhs.CoveredLines;
            that.TotalLines = lhs.TotalLines + rhs.TotalLines;
            return that;
        }

        public void Reset()
        {
            this.CoveredLines = 0;
            this.TotalLines = 0;
        }
    }
}

