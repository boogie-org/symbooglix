using System;

namespace Symbooglix
{
    namespace Util
    {
        /// <summary>
        /// Implementers of this Interface should
        /// dump a textual description of themselves
        /// to a TextWriter
        /// </summary>
        public interface IDumpable
        {
            void Dump(System.IO.TextWriter TW);
        }
    }
}

