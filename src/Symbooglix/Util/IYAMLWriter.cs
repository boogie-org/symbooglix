//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
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

