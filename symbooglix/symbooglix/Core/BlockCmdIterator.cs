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
            Debug.WriteLine("Entering block " + BB.Label);
            foreach (Cmd c in BB.Cmds)
            {
                Debug.WriteLine("tick");
                yield return c;
            }

            Debug.WriteLine("tick");
            yield return BB.TransferCmd;
        }

        System.Collections.IEnumerator System.Collections.IEnumerable.GetEnumerator ()
        {
            return GetEnumerator();
        }

    }
}

