//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2017 Daniel Liew
//
// This file is licensed under the MIT license.
// See LICENSE.txt for details.
//------------------------------------------------------------------------------
using System;
using System.Diagnostics;
using NUnit.Framework;

namespace SymbooglixLibTests
{
    public class AssertionTextWriterTraceListener : TextWriterTraceListener
    {
        public AssertionTextWriterTraceListener(System.IO.Stream stream) : base(stream)
        {

        }

        public AssertionTextWriterTraceListener(System.IO.TextWriter writer) : base(writer)
        {

        }
        

        public override void Fail(string message)
        {
            base.Fail(message);
            Assert.Fail(message);

        }

        public override void Fail(string message, string detailMessage)
        {
            base.Fail(message, detailMessage);
            Assert.Fail(message + " : " + detailMessage);
        }
    }
}

