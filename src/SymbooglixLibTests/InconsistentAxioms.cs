//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using NUnit.Framework;
using System;
using Symbooglix;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class InconsistentAxioms : SymbooglixTest
    {
        private void Init()
        {
            p = LoadProgramFrom("programs/InconsistentAxioms.bpl");
            this.e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
        }

        [Test(),ExpectedException(typeof(Symbooglix.InitialStateTerminated))]
        public void ExceptionThrown()
        {
            Init();
            e.Run(GetMain(p));

        }
    }


}

