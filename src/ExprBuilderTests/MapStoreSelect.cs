using System;
using System.Collections.Generic;
using NUnit.Framework;
using Microsoft.Boogie;
using Symbooglix;
using System.Linq;

using BPLType = Microsoft.Boogie.Type;

namespace ExprBuilderTests
{
    [TestFixture()]
    public class MapStoreSelect : IErrorSink
    {
        public MapStoreSelect()
        {
            // This is a hack
            SymbooglixLibTests.SymbooglixTest.SetupDebug();
            SymbooglixLibTests.SymbooglixTest.SetupCmdLineParser();
        }

        private IExprBuilder GetBuilder()
        {
            return new SimpleExprBuilder();
        }

        public void Error(IToken tok, string msg)
        {
            Assert.Fail(msg);
        }

        public void CheckType(Expr result, Predicate<BPLType> p)
        {
            Assert.IsTrue(p(result.ShallowType));
            Assert.IsNotNull(result.Type);
            Assert.IsTrue(p(result.Type));
            var TC = new TypecheckingContext(this);
            result.Typecheck(TC);
        }

        [TestCase()]
        public void SimpleMapSelect()
        {
            // var x:[int]bool;
            var id = GetMapVariable("x", BasicType.Bool, BasicType.Int).Item1;
            var builder = GetBuilder();

            // x[0]
            var result = builder.MapSelect(id, builder.ConstantInt(0));
            Assert.AreEqual("x[0]", result.ToString());
            CheckType(result, p => p.IsBool);
        }

        [TestCase(), ExpectedException(typeof(ExprTypeCheckException))]
        public void SimpleMapSelectWrongIndexType()
        {
            // var x:[bv8]bool;
            var id = GetMapVariable("x", BasicType.Bool, BasicType.GetBvType(8)).Item1;
            var builder = GetBuilder();

            // x[0]
            builder.MapSelect(id, builder.ConstantInt(0));
        }

        [TestCase(), ExpectedException(typeof(ArgumentException))]
        public void SimpleMapSelectWrongArity()
        {
            // var x:[bv8]bool;
            var id = GetMapVariable("x", BasicType.Bool, BasicType.Int, BasicType.Int).Item1;
            var builder = GetBuilder();

            // x[0]
            builder.MapSelect(id, builder.ConstantInt(0));
        }


        private Tuple<IdentifierExpr, BPLType> GetMapVariable(string name, BPLType resultTyp, params BPLType[] indices)
        {
            var mapType = new MapType(Token.NoToken,
                new List<Microsoft.Boogie.TypeVariable>(),
                indices.ToList(),
                resultTyp);
            var typeIdent = new TypedIdent(Token.NoToken, name, mapType);
            var gv = new GlobalVariable(Token.NoToken, typeIdent);
            var id = new IdentifierExpr(Token.NoToken, gv);

            var result = new Tuple<IdentifierExpr, BPLType>(id, mapType);
            return result;
        }

        [TestCase()]
        public void TwoIndicesMapSelect()
        {
            // var x:[int, int]bool;
            var id = GetMapVariable("x", BasicType.Bool, BasicType.Int, BasicType.Int).Item1;
            var builder = GetBuilder();

            // x[0, 1]
            var result = builder.MapSelect(id, builder.ConstantInt(0), builder.ConstantInt(1));
            Assert.AreEqual("x[0, 1]", result.ToString());
            CheckType(result, p => p.IsBool);
        }

        // FIXME: Boogie's typechecker actually seems to allow this. This seems crazy why would
        // you want a map without any arguments? You might as well just have a regular variable.
        [TestCase(),ExpectedException(typeof(ArgumentException))]
        public void NoIndicesMapSelect()
        {
            // var x:[]bool;
            var id = GetMapVariable("x", BasicType.Bool).Item1;
            var builder = GetBuilder();

            // x[]
            var result = builder.MapSelect(id);
            Assert.AreEqual("x[]", result.ToString());
            CheckType(result, p => p.IsBool);
        }

        [TestCase()]
        public void NestedMapSelect()
        {
            // var [int, int]bool; (we don't need the variable)
            var mapType = GetMapVariable("x", BasicType.Bool, BasicType.Int, BasicType.Int).Item2;

            // var y:[bool][int, int]bool;
            var vtPair = GetMapVariable("y", mapType, BasicType.Bool);
            var id = vtPair.Item1;

            var builder = GetBuilder();

            // y[true]
            var firstSelect = builder.MapSelect(id, builder.True);
            Assert.AreEqual("y[true]", firstSelect.ToString());
            CheckType(firstSelect, p => p.IsMap);
            Assert.AreEqual(mapType, firstSelect.Type);

            // y[true][0,1]
            var secondSelect = builder.MapSelect(firstSelect, builder.ConstantInt(0), builder.ConstantInt(1));
            Assert.AreEqual("y[true][0, 1]", secondSelect.ToString());
            CheckType(secondSelect, p => p.IsBool);
        }
    }
}

