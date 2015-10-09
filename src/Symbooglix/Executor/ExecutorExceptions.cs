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
using System.Collections.Generic;

namespace Symbooglix
{
    public class ExecutorException : Exception
    {
        public Executor TheExecutor{ get; private set;}
        public ExecutorException(Executor executor, string msg) : base(msg)
        {
            TheExecutor = executor;
        }
    }

    public class InitialStateTerminated : ExecutorException
    {
        public ExecutionState State { get; private set; }

        public InitialStateTerminated(Executor executor, ExecutionState state) : base(executor, "Cannot execute terminated state")
        {
            this.State = state;
        }
    }

    public class InvalidEntryPoint : ExecutorException
    {
        public Microsoft.Boogie.Implementation Impl { get; private set;}
        public InvalidEntryPoint(Executor executor, Microsoft.Boogie.Implementation impl) : base(executor, "Implementation in not a valid entry point")
        {
            this.Impl = impl;
        }
    }

    public class RecursiveFunctionDetectedException : ExecutorException
    {
        public IEnumerable<Microsoft.Boogie.Function> Functions;

        public RecursiveFunctionDetectedException(Executor executor, IEnumerable<Microsoft.Boogie.Function> functions): 
        base(executor, "Recursive functions detected")
        {
            this.Functions = functions;
        }
    }
}

