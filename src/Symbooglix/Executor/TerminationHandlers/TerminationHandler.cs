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
    public interface ITerminationHandler
    {
        void handleSuccess(ExecutionState s);
        void handleFailingAssert(ExecutionState s);
        void handleUnsatisfiableRequires(ExecutionState s, Microsoft.Boogie.Requires requiresStatement);
        void handleFailingEnsures(ExecutionState s, Microsoft.Boogie.Ensures ensuresStatement);
        void handleUnsatisfiableAssume(ExecutionState s);
    }
}

