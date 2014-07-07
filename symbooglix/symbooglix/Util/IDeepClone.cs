using System;

namespace Symbooglix
{
    namespace Util
    {
        public interface IDeepClone<T>
        {
            T DeepClone();
        }
    }
}

