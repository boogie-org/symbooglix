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
using Microsoft.Boogie;

namespace Symbooglix
{
    public interface ISymbolicPool : Util.IYAMLWriter
    {
        int Count { get; }
        SymbolicVariable GetFreshSymbolic(Variable Origin, ExecutionState owner);
        SymbolicVariable GetFreshSymbolic(HavocCmd cmd, int varsIndex, ExecutionState owner);
        SymbolicVariable GetFreshSymbolic(Procedure proc, int modSetIndex, ExecutionState owner);
    }
}

