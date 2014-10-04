using System;
using Microsoft.Boogie;
using System.IO;

namespace Symbooglix
{
    namespace Util
    {
        public class ProgramPrinter
        {
            public enum PrintType : int
            {
                // The values are hard coded here because they are the integer values
                // of ``CommandLineOptions.Clo.PrintUnstructured`` in Boogie
                STRUCTURED_ONLY = 0,
                STRUCTURED_AND_UNSTRUCTURED =1,
                UNSTRUCTURED_ONLY =2
            }

            static public void Print(Program prog, TextWriter TW, bool pretty, PrintType type)
            {
                // FIXME:
                // Urgh this is Gross! Fix boogie so we can request
                // printing an unstructured program cleanly
                // 0 = print only structured,  1 = both structured and unstructured,  2 = only unstructured
                CommandLineOptions.Clo.PrintUnstructured = (int) type;

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

