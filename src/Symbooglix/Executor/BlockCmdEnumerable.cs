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
using System.Collections.Generic;
using System.Collections;
using Microsoft.Boogie;
using System.Diagnostics;
using Symbooglix.Util;

namespace Symbooglix
{
    public class BlockCmdEnumerable : IEnumerable<Absy>
    {
        private Block BB;
        public BlockCmdEnumerable(Block BB)
        {
            this.BB = BB;
        }

        public IEnumerator<Absy> GetEnumerator()
        {
            return new BlockCmdEnumerator(BB);
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator ()
        {
            return GetEnumerator();
        }

    }

    // We use a manual implementation (rather than using a method that uses yield) so we
    // can do simple cloning. In the future it may be useful to support reverse iteration too.
    public class BlockCmdEnumerator : IEnumerator<Absy>
    {
        private Block BB;
        private int index;

        public int Count
        {
            get
            {
                return BB.Cmds.Count + 1 /*TransferCmd*/;
            }
        }

        public BlockCmdEnumerator(Block block)
        {
            BB = block;
            Reset();
        }

        public bool MoveNext()
        {
            ++index;

            if (index >= Count)
                return false; // Moved past last item
            else
                return true;
        }

        public void Reset()
        {
            index = -1;
        }

        public void Dispose()
        {
        }


        public Absy Current
        {
            get
            {
                if (index == -1)
                {
                    /* After an enumerator is created or after the Reset method is called, the MoveNext method must
                     * be called to advance the enumerator to the first element of the collection before reading the
                     * value of the Current property; otherwise, Current is undefined.
                     */
                    return null;
                }

                if (index >= Count)
                    throw new InvalidOperationException("Enumerator has moved past the end of available commands of the basic block");

                if (index < BB.Cmds.Count)
                    return BB.Cmds[index];
                else
                    return BB.TransferCmd;
            }
        }

        object IEnumerator.Current
        {
            get
            {
                return Current;
            }
        }

        public BlockCmdEnumerator Clone()
        {
            // The index is a value type so that will be a copy
            return (BlockCmdEnumerator) this.MemberwiseClone();
        }
    }
}

