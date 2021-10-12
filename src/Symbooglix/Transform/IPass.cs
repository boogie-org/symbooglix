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

