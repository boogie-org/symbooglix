using System;
using Microsoft.Boogie;
using System.IO;

namespace Symbooglix
{
    namespace Util
    {
        public class ProgramPrinter
        {
            static public void Print(Program prog, TextWriter TW, bool pretty, bool unstructured)
            {
                // FIXME:
                // Urgh this is Gross! Fix boogie so we can request
                // printing an unstructured program cleanly
                CommandLineOptions.Clo.PrintUnstructured = unstructured?1:0;

                // It is very important setTokens is false otherwise printing the program will cause the tokens
                // to change.
                using (var tokenWriter = new TokenTextWriter("", TW, /*setTokens=*/ false, pretty))
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

