using System;
using Microsoft.Boogie;
using Symbooglix;
using System.IO;

namespace ExprSMTLIBTest
{
    public class ExprSMTLIBTestBase
    {
        protected SMTLIBQueryPrinter GetPrinter(TextWriter TW)
        {
            return new SMTLIBQueryPrinter(TW, /*useNamedAttributeBindings=*/false, /*humanReadable=*/false, /*printTriggers=*/true);
        }
    }
}

