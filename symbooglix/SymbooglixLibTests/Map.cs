using NUnit.Framework;
using System;
using symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Map : SymbooglixTest
    {
        private class SimpleMapHandler : IBreakPointHandler
        {
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                throw new NotImplementedException();
            }
        }
        [Test()]
        public void SimpleMap()
        {
            p = loadProgram("programs/SimpleMap.bpl");
            e = getExecutor(p);
            var handler = new SimpleMapHandler();
            e.registerBreakPointHandler(handler);
            e.run(getMain(p));

        }

        private class TwoDMapHandler : IBreakPointHandler
        {
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                throw new NotImplementedException();
            }
        }
        [Test()]
        public void TwoDMap()
        {
            p = loadProgram("programs/2DMap.bpl");
            e = getExecutor(p);
            var handler = new TwoDMapHandler();
            e.registerBreakPointHandler(handler);
            e.run(getMain(p));

        }
    }
}

