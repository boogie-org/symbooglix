using System;

namespace symbooglix
{
    namespace util
    {
        public interface IDeepClone<T>
        {
            T DeepClone();
        }
    }
}

