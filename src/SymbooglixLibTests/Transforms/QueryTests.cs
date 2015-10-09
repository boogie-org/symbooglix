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
using Microsoft.Boogie;
using BPLType = Microsoft.Boogie.Type;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class QueryTests
    {
        [Test()]
        public void ShouldBeSame()
        {
            var builder = new SimpleExprBuilder(true);

            var dummyV = SymbooglixLibTests.MapProxyTests.GetVariable("dummy", BPLType.Int);
            // Hack
            dummyV.SetMetadata((int)Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(dummyV));
            var v = new SymbolicVariable("foo", dummyV);
            var id = builder.Identifier(v);

            var c0 = new Constraint(builder.Gt(id, builder.ConstantInt(0)));
            var c0Copy = new Constraint(builder.Gt(id, builder.ConstantInt(0)));
            var c1 = new Constraint(builder.Lt(id, builder.ConstantInt(10)));
            var c1Copy = new Constraint(builder.Lt(id, builder.ConstantInt(10)));

            var CM0 = new ConstraintManager();
            var CM1 = new ConstraintManager();

            CM0.AddConstraint(c0);
            CM0.AddConstraint(c1);
            CM1.AddConstraint(c0Copy);
            CM1.AddConstraint(c1Copy);

            var queryExpr0 = builder.Eq(id, builder.ConstantInt(5));
            var queryExpr1 = builder.Eq(id, builder.ConstantInt(5));

            var query0 = new Symbooglix.Solver.Query(CM0, new Constraint(queryExpr0));
            var query1 = new Symbooglix.Solver.Query(CM1, new Constraint(queryExpr1));

            Assert.AreEqual(query0.GetHashCode(), query1.GetHashCode());

            Assert.IsTrue(query0.Equals(query1));
        }

        [Test()]
        public void QueryExprDifferent()
        {
            var builder = new SimpleExprBuilder(true);

            var dummyV = SymbooglixLibTests.MapProxyTests.GetVariable("dummy", BPLType.Int);
            // Hack
            dummyV.SetMetadata((int)Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(dummyV));
            var v = new SymbolicVariable("foo", dummyV);
            var id = builder.Identifier(v);

            var c0 = new Constraint(builder.Gt(id, builder.ConstantInt(0)));
            var c0Copy = new Constraint(builder.Gt(id, builder.ConstantInt(0)));
            var c1 = new Constraint(builder.Lt(id, builder.ConstantInt(10)));
            var c1Copy = new Constraint(builder.Lt(id, builder.ConstantInt(10)));

            var CM0 = new ConstraintManager();
            var CM1 = new ConstraintManager();

            CM0.AddConstraint(c0);
            CM0.AddConstraint(c1);
            CM1.AddConstraint(c0Copy);
            CM1.AddConstraint(c1Copy);

            var queryExpr0 = builder.Eq(id, builder.ConstantInt(5));
            var queryExpr1 = builder.NotEq(id, builder.ConstantInt(5));

            var query0 = new Symbooglix.Solver.Query(CM0, new Constraint(queryExpr0));
            var query1 = new Symbooglix.Solver.Query(CM1, new Constraint(queryExpr1));

            Assert.AreNotEqual(query0.GetHashCode(), query1.GetHashCode());

            Assert.IsFalse(query0.Equals(query1));
        }

        [Test()]
        public void ConstraintDifferent()
        {
            var builder = new SimpleExprBuilder(true);

            var dummyV = SymbooglixLibTests.MapProxyTests.GetVariable("dummy", BPLType.Int);
            // Hack
            dummyV.SetMetadata((int)Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(dummyV));
            var v = new SymbolicVariable("foo", dummyV);
            var id = builder.Identifier(v);

            var c0 = new Constraint(builder.Gt(id, builder.ConstantInt(0)));
            var c0Copy = new Constraint(builder.Gt(id, builder.ConstantInt(0)));
            var c1 = new Constraint(builder.Lt(id, builder.ConstantInt(10)));
            var c1diff = new Constraint(builder.Le(id, builder.ConstantInt(10)));

            var CM0 = new ConstraintManager();
            var CM1 = new ConstraintManager();

            CM0.AddConstraint(c0);
            CM0.AddConstraint(c1);
            CM1.AddConstraint(c0Copy);
            CM1.AddConstraint(c1diff);

            var queryExpr0 = builder.Eq(id, builder.ConstantInt(5));
            var queryExpr1 = builder.Eq(id, builder.ConstantInt(5));

            var query0 = new Symbooglix.Solver.Query(CM0, new Constraint(queryExpr0));
            var query1 = new Symbooglix.Solver.Query(CM1, new Constraint(queryExpr1));

            Assert.AreNotEqual(query0.GetHashCode(), query1.GetHashCode());

            Assert.IsFalse(query0.Equals(query1));
        }
    }
}

