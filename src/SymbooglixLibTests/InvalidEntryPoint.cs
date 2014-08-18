using NUnit.Framework;
using System;
using Microsoft.Boogie;
using System.Collections.Generic;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class InvalidEntryPoint : SymbooglixTest
    {
        [ExpectedException(typeof(InvalidEntryPoint))]
        public void TestCase()
        {
            // It doesn't matter which program we load
            p = loadProgram("programs/assert_true.bpl");
            e = getExecutor(p);

            var impl = new Implementation(Token.NoToken, "dummy", null, null, null, null, new List<Block>());
            e.Run(impl);
        }
    }
}

