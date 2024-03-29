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
        public class PruneUnreachableBlocksPass : IPass
        {
            public PruneUnreachableBlocksPass()
            {
            }

            public string GetName()
            {
                return "Prune Unreachable Blocks Pass";
            }

            public void SetPassInfo(ref PassInfo passInfo)
            {
                return;
            }

            public bool RunOn(Microsoft.Boogie.Program prog, PassInfo passInfo)
            {
                foreach (var impl in prog.Implementations)
                {
                    impl.PruneUnreachableBlocks();
                }
                return true;
            }

            public void Reset()
            {
                // Nothing to do
            }
        }
    }
}

