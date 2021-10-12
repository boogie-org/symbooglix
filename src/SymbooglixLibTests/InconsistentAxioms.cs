//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2017 Daniel Liew
//
// This file is licensed under the MIT license.
// See LICENSE.txt for details.
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

