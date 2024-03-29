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
    public class DummyPass : Transform.IPass
    {
        public DummyPass()
        {
        }

        public bool RunOn(Microsoft.Boogie.Program prog, Transform.PassInfo passInfo)
        {
            return false;
        }

        public string GetName()
        {
            return "Dummy Pass";
        }

        public void SetPassInfo (ref Transform.PassInfo passInfo)
        {
            return;
        }

        public void Reset()
        {
        }
    }
}

