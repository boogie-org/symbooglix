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

        // FIXME: This is temporary remove as soon as possible
        public class IndentedTextWriterAdapter
        {
            public static void Write(System.IO.TextWriter TW, IYAMLWriter writer, string indent = "  ")
            {
                using (var ITW = new System.CodeDom.Compiler.IndentedTextWriter(TW, indent))
                {
                    writer.WriteAsYAML(ITW);
                }
            }
        }
    }
}

