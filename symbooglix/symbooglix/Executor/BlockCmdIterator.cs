using System;
using System.Collections.Generic;
using Microsoft.Boogie;
using System.Diagnostics;

namespace symbooglix
{
    public class BlockCmdIterator : IEnumerable<Absy>
    {
        private Block BB;
        public BlockCmdIterator(Block BB)
        {
            this.BB = BB;
        }

        public IEnumerator<Absy> GetEnumerator ()
        {
            foreach (Cmd c in BB.Cmds)
            {
                yield return c;
            }
            yield return BB.TransferCmd;
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator ()
        {
            return GetEnumerator();
        }

    }
}

