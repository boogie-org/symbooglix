using System;
using Microsoft.Boogie;
using System.IO;

namespace Symbooglix
{
    namespace Util
    {
        public class ProgramPrinter
        {
            static public void Print(Program prog, TextWriter TW, bool pretty)
            {
                using (var tokenWriter = new TokenTextWriter(TW, pretty))
                {
                    foreach (var tld in prog.TopLevelDeclarations)
                    {
                        tld.Emit(tokenWriter, 0);
                    }
                    TW.Flush();
                }

            }
        }
    }
}

