using System;

namespace Symbooglix
{
    public interface IExecutorEventHandler
    {
        void Connect(Executor e);
        void Disconnect(Executor e);
    }
}

