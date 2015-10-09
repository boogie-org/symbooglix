using System;

namespace Symbooglix
{
    namespace Util
    {
        public interface IYAMLWriter
        {
            void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW);
        }
    }
}

