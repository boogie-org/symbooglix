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
using System.Diagnostics;

namespace Symbooglix
{
    public class ExceptionThrowingTextWritierTraceListener : TextWriterTraceListener
    {
        public ExceptionThrowingTextWritierTraceListener(System.IO.Stream stream) : base(stream)
        {

        }

        public ExceptionThrowingTextWritierTraceListener(System.IO.TextWriter writer) : base(writer)
        {

        }


        public override void Fail(string message)
        {
            base.Fail(message);
            throw new AssertionFailingException(message);


        }

        public override void Fail(string message, string detailMessage)
        {
            base.Fail(message, detailMessage);
            throw new AssertionFailingException(message + " : " + detailMessage);
        }
    }

    public class AssertionFailingException : Exception
    {
        public AssertionFailingException(string msg) : base(msg) { }
    }
}

