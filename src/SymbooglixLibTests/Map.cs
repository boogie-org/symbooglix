using NUnit.Framework;
using System;
using Symbooglix;
using Microsoft.Basetypes;
using Microsoft.Boogie;
using System.Linq;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class Map : SymbooglixTest
    {
        private class SimpleMapHandler : IBreakPointHandler
        {
            public int hits = 0;
            private Expr intermediate = null;
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                if (name == "check_read_map")
                {
                    var a = e.CurrentState.GetInScopeVariableAndExprByName("a"); // a := symbolic_0[0bv8]
                    Assert.IsInstanceOfType(typeof(NAryExpr), a.Value);
                    NAryExpr mapSelect = a.Value as NAryExpr;
                    Assert.IsInstanceOfType(typeof(MapSelect), mapSelect.Fun);
                    Assert.AreEqual(2, mapSelect.Args.Count);

                    // [0] should be map Identifier
                    CheckIsSymbolicIdentifier(mapSelect.Args[0], e.CurrentState);

                    // [1] should be offset
                    CheckIsLiteralBVConstWithValue(mapSelect.Args[1], BigNum.FromInt(0));
                }
                else if (name == "check_write_literal")
                {
                    var m = e.CurrentState.GetInScopeVariableAndExprByName("m"); // m := symbolic_0[3bv8 := 12bv32]
                    Assert.IsInstanceOfType(typeof(NAryExpr), m.Value);
                    NAryExpr mapStore = m.Value as NAryExpr;
                    Assert.IsInstanceOfType(typeof(MapStore), mapStore.Fun);
                    Assert.AreEqual(3, mapStore.Args.Count);

                    // [0] should be map Identifier
                    CheckIsSymbolicIdentifier(mapStore.Args[0], e.CurrentState);

                    // [1] should be write offset
                    CheckIsLiteralBVConstWithValue(mapStore.Args[1], BigNum.FromInt(3));

                    // [2] should be value written to location in Map
                    CheckIsLiteralBVConstWithValue(mapStore.Args[2], BigNum.FromInt(12));

                }
                else if (name == "check_write_from_map")
                {
                    var m = e.CurrentState.GetInScopeVariableAndExprByName("m");
                    intermediate = (Expr) new Duplicator().Visit(m.Value); // Save a copy of the expression for later.
                    Assert.IsInstanceOfType(typeof(NAryExpr), m.Value);
                    NAryExpr mapStore = m.Value as NAryExpr;
                    Assert.IsInstanceOfType(typeof(MapStore), mapStore.Fun); // symbolic_0[3bv8:= 12bv32][1bv8 := symbolic_0[0bv8]]
                    Assert.AreEqual(3, mapStore.Args.Count);

                    // [0] Is Map written to which should we wrote to earlier so should also be MapStore
                    // FIXME: Store duplicate of intermediate when doing check_write_literal and just compare against that to simplify test
                    Assert.IsInstanceOfType(typeof(NAryExpr), mapStore.Args[0]);
                    NAryExpr writtenTo = mapStore.Args[0] as NAryExpr; // symbolic_0[3bv8:=12bv32]
                    Assert.IsInstanceOfType(typeof(MapStore), writtenTo.Fun);

                    {
                        // [0] should be map Identifier
                        CheckIsSymbolicIdentifier(writtenTo.Args[0], e.CurrentState);

                        // [1] should be write offset
                        CheckIsLiteralBVConstWithValue(writtenTo.Args[1], BigNum.FromInt(3));

                        // [2] should be value written to location in Map
                        CheckIsLiteralBVConstWithValue(writtenTo.Args[2], BigNum.FromInt(12));
                    }

                    // [1] is write offset
                    CheckIsLiteralBVConstWithValue(mapStore.Args[1], BigNum.FromInt(1)); // 1bv8

                    // [2] is value to write which is actually a value inside own map
                    Assert.IsInstanceOfType(typeof(NAryExpr), mapStore.Args[2]);
                    NAryExpr WrittenValue = mapStore.Args[2] as NAryExpr; // symbolic_0[0bv8]
                    Assert.IsInstanceOfType(typeof(MapSelect), WrittenValue.Fun);


                    {
                        // [0] should be map Identifier
                        CheckIsSymbolicIdentifier(WrittenValue.Args[0], e.CurrentState);

                        // [1] should be offset
                        CheckIsLiteralBVConstWithValue(WrittenValue.Args[1], BigNum.FromInt(0));
                    }
                }
                else if (name == "check_write_symbolic_index")
                {
                    // Expecting m := symbolic_0[3bv8 := 12bv32][1bv8 := symbolic_0[0bv8]][symbolic_2 := 7bv32]
                    var m = e.CurrentState.GetInScopeVariableAndExprByName("m");
                    Assert.IsInstanceOfType(typeof(NAryExpr), m.Value);
                    NAryExpr mapStore = m.Value as NAryExpr;
                    Assert.IsInstanceOfType(typeof(MapStore), mapStore.Fun); // symbolic_0[3bv8:= 12bv32][1bv8 := symbolic_0[0bv8]]
                    Assert.AreEqual(3, mapStore.Args.Count);

                    // [0] Should be the map written to which should be equivalent to the expression recorded in "intermediate"
                    Assert.IsNotNull(intermediate);
                    //Assert.IsTrue(intermediate.Equals(mapStore.Args[0])); // FIXME: Structual equality is broken in Boogie!

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
                return Executor.HandlerAction.CONTINUE;
            }
        }
        [Test()]
        public void SimpleMap()
        {
            p = loadProgram("programs/SimpleMap.bpl");
            e = getExecutor(p);
            var handler = new SimpleMapHandler();
            e.RegisterBreakPointHandler(handler);
            e.Run(getMain(p));
            Assert.AreEqual(4, handler.hits);

        }

        private class TwoDMapHandler : IBreakPointHandler
        {
            public Executor.HandlerAction handleBreakPoint(string name, Executor e)
            {
                throw new NotImplementedException();
            }
        }
        [Test()]
        public void TwoDMap()
        {
            p = loadProgram("programs/2DMap.bpl");
            e = getExecutor(p);
            var handler = new TwoDMapHandler();
            e.RegisterBreakPointHandler(handler);
            e.Run(getMain(p));

        }
    }
}

