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

namespace Symbooglix
{
    public interface IExecutorEventHandler
    {
        void Connect(Executor e);
        void Disconnect(Executor e);
    }
}

