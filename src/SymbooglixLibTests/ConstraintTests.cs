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
    public class ConstraintTests
    {
        [Test()]
        public void ShouldBeIdentical()
        {
            var builder = new SimpleExprBuilder(true);

            var dummyV = SymbooglixLibTests.MapProxyTests.GetVariable("dummy", BPLType.Int);
            // Hack
            dummyV.SetMetadata((int)Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(dummyV));
            var v = new SymbolicVariable("foo", dummyV);

            var c0 = new Constraint(builder.Lt(builder.Identifier(v), builder.ConstantInt(5)));
            var c1 = new Constraint(builder.Lt(builder.Identifier(v), builder.ConstantInt(5)));
            Assert.AreEqual(c0.GetHashCode(), c1.GetHashCode());
            Assert.IsTrue(c0.Equals(c1));

            // Check used variables
            Assert.AreEqual(1, c0.UsedVariables.Count);
            Assert.AreEqual(1, c1.UsedVariables.Count);
            Assert.IsTrue(c0.UsedVariables.Contains(v));
            Assert.IsTrue(c1.UsedVariables.Contains(v));

            Assert.AreEqual(0, c0.UsedUninterpretedFunctions.Count);
            Assert.AreEqual(0, c1.UsedUninterpretedFunctions.Count);
        }

        [Test()]
        public void ShouldNotBeIdentical()
        {
            var builder = new SimpleExprBuilder(true);

            var dummyV = SymbooglixLibTests.MapProxyTests.GetVariable("dummy", BPLType.Int);
            // Hack
            dummyV.SetMetadata((int)Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(dummyV));
            var v = new SymbolicVariable("foo", dummyV);

            var c0 = new Constraint(builder.Lt(builder.Identifier(v), builder.ConstantInt(5)));
            var c1 = new Constraint(builder.Gt(builder.Identifier(v), builder.ConstantInt(5)));
            Assert.AreNotEqual(c0.GetHashCode(), c1.GetHashCode());
            Assert.IsFalse(c0.Equals(c1));
        }
    }
}

