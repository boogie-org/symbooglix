using System;

namespace Symbooglix
{
    public class DummyPass : Transform.IPass
    {
        public DummyPass()
        {
        }

        public bool RunOn(Microsoft.Boogie.Program prog)
        {
            return false;
        }

        public string GetName()
        {
            return "Dummy Pass";
        }

        public void SetPassInfo (ref Transform.PassInfo passInfo)
        {
            return;
        }
    }
}

