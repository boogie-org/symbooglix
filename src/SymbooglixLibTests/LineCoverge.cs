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
using NUnit.Framework;
using Symbooglix;
using System.Linq;
using Microsoft.Boogie;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class LineCoverge : SymbooglixTest
    {
        [Test()]
        public void singlePath()
        {
            p = LoadProgramFrom(@"
            const g:int;
            axiom g == 0;
            
            procedure main() returns (r:int)
            requires g == 0;
            ensures r == 0;
            {
                r:= 0;
                r:= g;
                return;
            }

            ", "test.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var tc = new TerminationCounter(TerminationCounter.CountType.ONLY_NON_SPECULATIVE);
            tc.Connect(e);

            e.Run(GetMain(p));
            Assert.AreEqual(1, tc.NumberOfTerminatedStates);
            Assert.AreEqual(1, tc.Sucesses);

            var progCoverage = p.GetLineCoverage();
            Assert.AreEqual(6, progCoverage.TotalLines);
            Assert.AreEqual(6, progCoverage.CoveredLines);
        }

        [Test()]
        public void multiplePathReachable()
        {
            p = LoadProgramFrom(@"
            const g:int;
            axiom g == 0;
            
            procedure main() returns (r:int)
            requires g == 0;
            ensures r == 0;
            {
                var flag:bool;
                entry:
                    goto thenC, elseC;
                
                thenC:
                    assume flag;
                    r := 0;
                    goto exit;
                elseC:
                    assume !flag;
                    r := 1;
                    assert true;
                    goto exit;

                exit:
                    r := g;
                    assert true;
                    assert true;
                    return;
            }

            ", "test.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var tc = new TerminationCounter(TerminationCounter.CountType.ONLY_NON_SPECULATIVE);
            tc.Connect(e);

            e.Run(GetMain(p));
            Assert.AreEqual(2, tc.NumberOfTerminatedStates);
            Assert.AreEqual(2, tc.Sucesses);

            // Check Implementation coverage
            var implCoverage = p.TopLevelDeclarations.OfType<Implementation>().First().GetLineCoverage();
            Assert.AreEqual(12, implCoverage.TotalLines);
            Assert.AreEqual(12, implCoverage.CoveredLines);

            // Check Procedure coverage
            var procCoverage = p.TopLevelDeclarations.OfType<Procedure>().First().GetLineCoverage();
            Assert.AreEqual(2, procCoverage.TotalLines);
            Assert.AreEqual(2, procCoverage.CoveredLines);

            // Check program coverage
            var progCoverage = p.GetLineCoverage();
            Assert.AreEqual(15, progCoverage.TotalLines);
            Assert.AreEqual(15, progCoverage.CoveredLines);
        }

        [Test()]
        public void multiplePathNotAllReachable()
        {
            p = LoadProgramFrom(@"
            const g:int;
            axiom g == 0;
            
            procedure main() returns (r:int)
            requires g == 0;
            ensures r == 0;
            {
                var flag:bool;
                entry:
                    flag := true;
                    goto thenC, elseC;
                
                thenC:
                    assume flag;
                    r := 0;
                    goto exit;
                elseC:
                    assume !flag;
                    r := 1;
                    assert true;
                    goto exit;

                exit:
                    r := g;
                    assert true;
                    assert true;
                    return;
            }

            ", "test.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var tc = new TerminationCounter(TerminationCounter.CountType.ONLY_NON_SPECULATIVE);
            tc.Connect(e);

            e.Run(GetMain(p));
            Assert.AreEqual(1, tc.NumberOfTerminatedStates);
            Assert.AreEqual(1, tc.Sucesses);

            // Check Implementation coverage
            var implCoverage = p.TopLevelDeclarations.OfType<Implementation>().First().GetLineCoverage();
            Assert.AreEqual(13, implCoverage.TotalLines);
            Assert.AreEqual(9, implCoverage.CoveredLines);

            // Check Procedure coverage
            var procCoverage = p.TopLevelDeclarations.OfType<Procedure>().First().GetLineCoverage();
            Assert.AreEqual(2, procCoverage.TotalLines);
            Assert.AreEqual(2, procCoverage.CoveredLines);

            // Check program coverage
            var progCoverage = p.GetLineCoverage();
            Assert.AreEqual(16, progCoverage.TotalLines);
            Assert.AreEqual(12, progCoverage.CoveredLines);
        }

        [Test()]
        public void multiplePathsUncalledProcedure()
        {
            p = LoadProgramFrom(@"
            const g:int;
            axiom g == 0;

            procedure foo();
            requires g == 0;
            ensures g == 0;
            
            procedure main() returns (r:int)
            requires g == 0;
            ensures r == 0;
            {
                var flag:bool;
                entry:
                    goto thenC, elseC;
                
                thenC:
                    assume flag;
                    r := 0;
                    goto exit;
                elseC:
                    assume !flag;
                    r := 1;
                    assert true;
                    goto exit;

                exit:
                    r := g;
                    assert true;
                    assert true;
                    return;
            }

            ", "test.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());

            var tc = new TerminationCounter(TerminationCounter.CountType.ONLY_NON_SPECULATIVE);
            tc.Connect(e);

            e.Run(GetMain(p));
            Assert.AreEqual(2, tc.NumberOfTerminatedStates);
            Assert.AreEqual(2, tc.Sucesses);

            // Check Implementation coverage
            var implCoverage = p.TopLevelDeclarations.OfType<Implementation>().First().GetLineCoverage();
            Assert.AreEqual(12, implCoverage.TotalLines);
            Assert.AreEqual(12, implCoverage.CoveredLines);

            // Check Procedure coverage
            var procCoverage = p.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.Name == "main").First().GetLineCoverage();
            Assert.AreEqual(2, procCoverage.TotalLines);
            Assert.AreEqual(2, procCoverage.CoveredLines);

            var procFooCoverage = p.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.Name == "foo").First().GetLineCoverage();
            Assert.AreEqual(2, procFooCoverage.TotalLines);
            Assert.AreEqual(0, procFooCoverage.CoveredLines);

            // Check program coverage
            var progCoverage = p.GetLineCoverage();
            Assert.AreEqual(17, progCoverage.TotalLines);
            Assert.AreEqual(15, progCoverage.CoveredLines);
        }

        [Test()]
        public void multiplePathsCalledProcedure()
        {
            p = LoadProgramFrom(@"
            const g:int;
            axiom g == 0;

            procedure foo();
            requires g == 0;
            ensures g == 0;
            
            procedure main() returns (r:int)
            requires g == 0;
            ensures r == 0;
            {
                var flag:bool;
                entry:
                    flag := false;
                    goto thenC, elseC;
                
                thenC:
                    assume flag;
                    r := 0;
                    goto exit;
                elseC:
                    assume !flag;
                    r := 1;
                    assert true;
                    call foo();
                    goto exit;

                exit:
                    r := g;
                    assert true;
                    assert true;
                    return;
            }

            ", "test.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var tc = new TerminationCounter(TerminationCounter.CountType.ONLY_NON_SPECULATIVE);
            tc.Connect(e);

            e.Run(GetMain(p));
            Assert.AreEqual(1, tc.NumberOfTerminatedStates);
            Assert.AreEqual(1, tc.Sucesses);

            // Check Implementation coverage
            var implCoverage = p.TopLevelDeclarations.OfType<Implementation>().First().GetLineCoverage();
            Assert.AreEqual(14, implCoverage.TotalLines);
            Assert.AreEqual(11, implCoverage.CoveredLines);

            // Check Procedure coverage
            var procCoverage = p.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.Name == "main").First().GetLineCoverage();
            Assert.AreEqual(2, procCoverage.TotalLines);
            Assert.AreEqual(2, procCoverage.CoveredLines);

            var procFooCoverage = p.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.Name == "foo").First().GetLineCoverage();
            Assert.AreEqual(2, procFooCoverage.TotalLines);
            Assert.AreEqual(2, procFooCoverage.CoveredLines);

            // Check program coverage
            var progCoverage = p.GetLineCoverage();
            Assert.AreEqual(19, progCoverage.TotalLines);
            Assert.AreEqual(16, progCoverage.CoveredLines);
        }

        [Test()]
        public void multiplePathsCalledImplementation()
        {
            p = LoadProgramFrom(@"
            const g:int;
            axiom g == 0;

            procedure foo()
            requires g == 0;
            ensures g == 0;
            {
                return;
            }
            
            procedure main() returns (r:int)
            requires g == 0;
            ensures r == 0;
            {
                var flag:bool;
                entry:
                    flag := false;
                    goto thenC, elseC;
                
                thenC:
                    assume flag;
                    r := 0;
                    goto exit;
                elseC:
                    assume !flag;
                    r := 1;
                    assert true;
                    call foo();
                    goto exit;

                exit:
                    r := g;
                    assert true;
                    assert true;
                    return;
            }

            ", "test.bpl");
            e = GetExecutor(p, new DFSStateScheduler(), GetSolver());
            e.UseGotoLookAhead = true;

            var tc = new TerminationCounter(TerminationCounter.CountType.ONLY_NON_SPECULATIVE);
            tc.Connect(e);

            e.Run(GetMain(p));
            Assert.AreEqual(1, tc.NumberOfTerminatedStates);
            Assert.AreEqual(1, tc.Sucesses);

            // Check Implementation coverage
            var implCoverage = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First().GetLineCoverage();
            Assert.AreEqual(14, implCoverage.TotalLines);
            Assert.AreEqual(11, implCoverage.CoveredLines);

            var implFooCoverage = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "foo").First().GetLineCoverage();
            Assert.AreEqual(1, implFooCoverage.TotalLines);
            Assert.AreEqual(1, implFooCoverage.CoveredLines);

            // Check Procedure coverage
            var procCoverage = p.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.Name == "main").First().GetLineCoverage();
            Assert.AreEqual(2, procCoverage.TotalLines);
            Assert.AreEqual(2, procCoverage.CoveredLines);

            var procFooCoverage = p.TopLevelDeclarations.OfType<Procedure>().Where(proc => proc.Name == "foo").First().GetLineCoverage();
            Assert.AreEqual(2, procFooCoverage.TotalLines);
            Assert.AreEqual(2, procFooCoverage.CoveredLines);

            // Check program coverage
            var progCoverage = p.GetLineCoverage();
            Assert.AreEqual(20, progCoverage.TotalLines);
            Assert.AreEqual(17, progCoverage.CoveredLines);
        }
    }
}

