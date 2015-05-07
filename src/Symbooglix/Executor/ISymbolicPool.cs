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

