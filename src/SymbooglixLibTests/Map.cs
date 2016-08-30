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
using Microsoft.Basetypes;
using Microsoft.Boogie;
using System.Linq;
using System.Collections.Generic;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Map : SymbooglixTest
    {
        [Test()]
        public void SimpleMap()
        {
            int hits = 0;
            Expr nestedMapStoreintermediate = null;
            Expr simpleMapStoreIntermediate = null;
            p = LoadProgramFrom("programs/SimpleMap.bpl");
            e = GetExecutor(p);
            var builderDuplicator = new BuilderDuplicator( new SimpleExprBuilder(/*immutable=*/ true));
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                if (data.Name == "check_read_map")
                {
                    var a = e.CurrentState.GetInScopeVariableAndExprByName("a"); // a := symbolic_0[0bv8]
                    Assert.IsInstanceOf<NAryExpr>(a.Value);
                    NAryExpr mapSelect = a.Value as NAryExpr;
                    Assert.IsInstanceOf<MapSelect>(mapSelect.Fun);
                    Assert.AreEqual(2, mapSelect.Args.Count);

                    // [0] should be map Identifier
                    CheckIsSymbolicIdentifier(mapSelect.Args[0], e.CurrentState);

                    // [1] should be offset
                    CheckIsLiteralBVConstWithValue(mapSelect.Args[1], BigNum.FromInt(0));
                }
                else if (data.Name == "check_write_literal")
                {
                    var m = e.CurrentState.GetInScopeVariableAndExprByName("m"); // m := symbolic_0[3bv8 := 12bv32]
                    simpleMapStoreIntermediate = (Expr) builderDuplicator.Visit(m.Value); // Save a copy of the expression for later.
                    Assert.IsInstanceOf<NAryExpr>(m.Value);
                    NAryExpr mapStore = m.Value as NAryExpr;
                    Assert.IsInstanceOf<MapStore>(mapStore.Fun);
                    Assert.AreEqual(3, mapStore.Args.Count);

                    // [0] should be map Identifier
                    CheckIsSymbolicIdentifier(mapStore.Args[0], e.CurrentState);

                    // [1] should be write offset
                    CheckIsLiteralBVConstWithValue(mapStore.Args[1], BigNum.FromInt(3));

                    // [2] should be value written to location in Map
                    CheckIsLiteralBVConstWithValue(mapStore.Args[2], BigNum.FromInt(12));

                }
                else if (data.Name == "check_write_from_map")
                {
                    var m = e.CurrentState.GetInScopeVariableAndExprByName("m");
                    nestedMapStoreintermediate = (Expr) builderDuplicator.Visit(m.Value); // Save a copy of the expression for later.
                    Assert.IsInstanceOf<NAryExpr>(m.Value);
                    NAryExpr mapStore = m.Value as NAryExpr;
                    Assert.IsInstanceOf<MapStore>(mapStore.Fun); // symbolic_0[3bv8:= 12bv32][1bv8 := symbolic_0[0bv8]]
                    Assert.AreEqual(3, mapStore.Args.Count);

                    // [0] Is Map written to which should we wrote to earlier so should also be MapStore
                    Assert.IsTrue(mapStore.Args[0].Equals(simpleMapStoreIntermediate));


                    // [1] is write offset
                    CheckIsLiteralBVConstWithValue(mapStore.Args[1], BigNum.FromInt(1)); // 1bv8

                    // [2] is value to write which is actually a value inside own map
                    Assert.IsInstanceOf<NAryExpr>(mapStore.Args[2]);
                    NAryExpr WrittenValue = mapStore.Args[2] as NAryExpr; // symbolic_0[0bv8]
                    Assert.IsInstanceOf<MapSelect>(WrittenValue.Fun);


                    {
                        // [0] should be map Identifier
                        CheckIsSymbolicIdentifier(WrittenValue.Args[0], e.CurrentState);

                        // [1] should be offset
                        CheckIsLiteralBVConstWithValue(WrittenValue.Args[1], BigNum.FromInt(0));
                    }
                }
                else if (data.Name == "check_write_symbolic_index")
                {
                    // Expecting m := symbolic_0[3bv8 := 12bv32][1bv8 := symbolic_0[0bv8]][symbolic_2 := 7bv32]
                    var m = e.CurrentState.GetInScopeVariableAndExprByName("m");
                    Assert.IsInstanceOf<NAryExpr>(m.Value);
                    NAryExpr mapStore = m.Value as NAryExpr;
                    Assert.IsInstanceOf<MapStore>(mapStore.Fun); // symbolic_0[3bv8:= 12bv32][1bv8 := symbolic_0[0bv8]]
                    Assert.AreEqual(3, mapStore.Args.Count);

                    // [0] Should be the map written to which should be equivalent to the expression recorded in "intermediate"
                    Assert.IsNotNull(nestedMapStoreintermediate);
                    Assert.IsTrue(nestedMapStoreintermediate.Equals(mapStore.Args[0]));

                    // [1] Write offset which should be symbolic (symbolic_2)
                    CheckIsSymbolicIdentifier(mapStore.Args[1], e.CurrentState);

                    // [2] Value to write (7bv32)
                    CheckIsLiteralBVConstWithValue(mapStore.Args[2], BigNum.FromInt(7));
                }
                else
                {
                    Assert.Fail("Unsupported break point");
                }

                ++hits;
            };
            e.Run(GetMain(p));
            Assert.AreEqual(4, hits);

        }

        [Test()]
        public void PartialIndexMap()
        {
            p = LoadProgramFrom(@"
            procedure main()
            {
                var x:[int][int]bool;
                var y:[int][int]bool;
                var symIndex:int;
                x[0][0] := false;
                // only partially index into y
                y[0] := x[0];
                assert {:symbooglix_bp ""check_written""} true;
            }

            ", "test.bpl");

            e = GetExecutor(p);
            bool check_written = false;
            var builder = new SimpleExprBuilder(true);
            var localVarX = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First().LocVars.Where(v => v.Name == "x").First();
            var localVarY = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First().LocVars.Where(v => v.Name == "y").First();
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArgs)
            {
                Assert.AreEqual("check_written", eventArgs.Name);
                check_written = true;

                // Check we can read x[0][0] directly
                var x00 = e.CurrentState.ReadMapVariableInScopeAt(localVarX, new List<Expr>() {
                    builder.ConstantInt(0),
                    builder.ConstantInt(0)
                });
                Assert.AreEqual(builder.False, x00);

                var yExpr = e.CurrentState.GetInScopeVariableExpr(localVarY);
                Assert.AreEqual("~sb_y_0[0 := ~sb_x_0[0 := ~sb_x_0[0][0 := false]][0]]", yExpr.ToString());
            };
            e.Run(GetMain(p));
            Assert.IsTrue(check_written);
        }

        [Test()]
        public void ConcreteMapAssign()
        {
            p = LoadProgramFrom(@"
            procedure main()
            {
                var x:[int][int]bool;
                var symIndex:int;
                x[0][0] := true;
                x[0][1] := false;
                assert {:symbooglix_bp ""check_written""} true;

                // write to symbolic location
                x[0][symIndex] := false;

                assert {:symbooglix_bp ""check_sym_write""} true;
            }

            ", "test.bpl");

            e = GetExecutor(p);
            bool check_written = false;
            bool check_sym_write = false;
            var builder = new SimpleExprBuilder(true);
            var localVarV = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First().LocVars.Where(v => v.Name == "x").First();
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArgs)
            {
                switch (eventArgs.Name)
                {
                    case "check_written":
                        check_written = true;


                        // Check we can read x[0][0] directly
                        var x00 = e.CurrentState.ReadMapVariableInScopeAt(localVarV, new List<Expr>() { builder.ConstantInt(0), builder.ConstantInt(0) });
                        Assert.AreEqual(builder.True, x00);
                        var x01 = e.CurrentState.ReadMapVariableInScopeAt(localVarV, new List<Expr>() { builder.ConstantInt(0), builder.ConstantInt(1) } );
                        Assert.AreEqual(builder.False, x01);

                        // Check the flushed expression from
                        // Note without the constant folding expr builder the form is
                        // "~sb_x_0[0 := ~sb_x_0[0][0 := true]][0 := ~sb_x_0[0 := ~sb_x_0[0][0 := true]][0][1 := false]]"
                        Assert.AreEqual("~sb_x_0[0 := ~sb_x_0[0][0 := true][1 := false]]",
                                        e.CurrentState.GetInScopeVariableExpr(localVarV).ToString());
                        break;
                    case "check_sym_write":
                        check_sym_write = true;

                        var x00After = e.CurrentState.ReadMapVariableInScopeAt(localVarV, new List<Expr>() { builder.ConstantInt(0), builder.ConstantInt(0) });
                        Console.WriteLine(x00After.ToString());
                        // FIXME: I'm unsure if this is correct
                        Console.WriteLine(x00After.ToString());
                        Assert.AreEqual("~sb_x_0[0][0 := true][1 := false][~sb_symIndex_0 := false][0]",
                            x00After.ToString());
                        break;
                    default:
                        Assert.Fail("Unexpected breakpoint");
                        break;
                }

            };
            e.Run(GetMain(p));

            Assert.IsTrue(check_written);
            Assert.IsTrue(check_sym_write);
        }

        [Test()]
        public void DirectMapCopy()
        {
            p = LoadProgramFrom(@"
            procedure main()
            {
                var x:[int]bool;
                var y:[int]bool;
                x[0] := true;
                x[1] := false;
                assert {:symbooglix_bp ""check_written""} true;

                // copy the map
                y := x;

                assert {:symbooglix_bp ""check_map_copy""} true;
            }

            ", "test.bpl");

            e = GetExecutor(p);
            bool check_written = false;
            bool check_map_copy = false;
            var builder = new SimpleExprBuilder(true);
            var localVarX = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First().LocVars.Where(v => v.Name == "x").First();
            var localVarY = p.TopLevelDeclarations.OfType<Implementation>().Where(i => i.Name == "main").First().LocVars.Where(v => v.Name == "y").First();
            e.BreakPointReached += delegate(object sender, Executor.BreakPointEventArgs eventArgs)
            {
                switch (eventArgs.Name)
                {
                    case "check_written":
                        check_written = true;

                        // Check we can read x[0] and x[1] directly
                        var x0 = e.CurrentState.ReadMapVariableInScopeAt(localVarX, new List<Expr>() { builder.ConstantInt(0) });
                        Assert.AreEqual(builder.True, x0);
                        var x1 = e.CurrentState.ReadMapVariableInScopeAt(localVarX, new List<Expr>() { builder.ConstantInt(1) } );
                        Assert.AreEqual(builder.False, x1);

                        // Check the full expression form
                        Assert.AreEqual("~sb_x_0[0 := true][1 := false]", e.CurrentState.GetInScopeVariableExpr(localVarX).ToString());
                        break;
                    case "check_map_copy":
                        check_map_copy = true;

                        // Check we can read y[0] and y[1] directly
                        var y0 = e.CurrentState.ReadMapVariableInScopeAt(localVarY, new List<Expr>() { builder.ConstantInt(0) });
                        Assert.AreEqual(builder.True, y0);
                        var y1 = e.CurrentState.ReadMapVariableInScopeAt(localVarY, new List<Expr>() { builder.ConstantInt(1) } );
                        Assert.AreEqual(builder.False, y1);

                        // Check the full expression form
                        Assert.AreEqual("~sb_x_0[0 := true][1 := false]", e.CurrentState.GetInScopeVariableExpr(localVarX).ToString());
                        Assert.AreEqual("~sb_x_0[0 := true][1 := false]", e.CurrentState.GetInScopeVariableExpr(localVarY).ToString());

                        break;
                    default:
                        Assert.Fail("Unexpected breakpoint");
                        break;
                }
            };
            e.Run(GetMain(p));
            Assert.IsTrue(check_written);
            Assert.IsTrue(check_map_copy);
        }

        [Test()]
        public void AxiomOnMap()
        {
            p = LoadProgramFrom(@"
            const g:[int]bool;
            // the bound variable here is the index into a map
            axiom (exists x:int :: (x == 0) && g[x]);

            procedure main() {
              assert g[0];
            }
            ", "test.bpl");
            e = GetExecutor(p, /*scheduler=*/ new DFSStateScheduler(), /*solver=*/ GetSolver());
            var tc = new TerminationCounter(TerminationCounter.CountType.BOTH);
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(1, tc.Sucesses);
            Assert.AreEqual(0, tc.FailingAsserts);
        }

        [Test()]
        public void AxiomOnMap2()
        {
            p = LoadProgramFrom(@"
            const g:[int]bool;
            // the bound variable here is a map
            axiom (exists m:[int]bool :: m[0] == g[0]);

            procedure main() {
              assert g[0] || !g[0];
            }
            ", "test.bpl");
            e = GetExecutor(p, /*scheduler=*/ new DFSStateScheduler(), /*solver=*/ GetSolver());
            var tc = new TerminationCounter(TerminationCounter.CountType.BOTH);
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(1, tc.Sucesses);
            Assert.AreEqual(0, tc.FailingAsserts);
        }

        [Test(),Ignore()]
        public void TwoDMap()
        {
            p = LoadProgramFrom("programs/2DMap.bpl");
            e = GetExecutor(p);
            e.BreakPointReached += delegate(object executor, Executor.BreakPointEventArgs data)
            {
                throw new NotImplementedException();
            };
            e.Run(GetMain(p));

        }

        [Test()]
        public void MultiArityMapMixedTypes()
        {
            p = LoadProgramFrom(@"
            procedure main() {
              var x:[int,bool]bool;

              x[0,false] := true;
              assert x[0,false] == true;
            }
            ", "test.bpl");
            e = GetExecutor(p, /*scheduler=*/ new DFSStateScheduler(), /*solver=*/ GetSolver());
            var tc = new TerminationCounter(TerminationCounter.CountType.BOTH);
            tc.Connect(e);
            e.Run(GetMain(p));
            Assert.AreEqual(1, tc.Sucesses);
            Assert.AreEqual(0, tc.FailingAsserts);
        }
    }
}

