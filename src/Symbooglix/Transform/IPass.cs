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
using System.Collections.Generic;

namespace Symbooglix
{
    namespace Transform
    {
        public interface IPass
        {
            string GetName();
            void SetPassInfo(ref PassInfo passInfo);
            bool RunOn(Program prog, PassInfo passInfo);
            void Reset();
        }
    }
}

