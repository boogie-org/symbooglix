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
    public abstract class AbstractExecutorFileLogger : IExecutorEventHandler
    {
        // Deliberately not using a property because setting needs
        // to be overridable.
        protected string Directory;


        public AbstractExecutorFileLogger()
        {
            Directory = "";
        }

        public virtual void SetDirectory(string directory)
        {
            this.Directory = directory;
        }

        public string GetDirectory()
        {
            return this.Directory;
        }

        public abstract void Connect(Executor e);
        public abstract void Disconnect(Executor e);
    }
}

