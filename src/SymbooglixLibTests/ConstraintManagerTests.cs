using System;
using NUnit.Framework;
using Symbooglix;
using Microsoft.Boogie;
using BPLType = Microsoft.Boogie.Type;
using System.Collections.Generic;

namespace SymbooglixLibTests
{
    [TestFixture()]
    public class ConstraintManagerTests
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
            Assert.AreEqual(0, CM0.GetHashCode());
            CM0.AddConstraint(c0);
            var firstHashCode = CM0.GetHashCode();
            CM0.AddConstraint(c1);
            Assert.AreNotEqual(firstHashCode, CM0.GetHashCode());

            var CM1 = new ConstraintManager();
            CM1.AddConstraint(c0Copy);
            Assert.AreEqual(firstHashCode, CM1.GetHashCode());
            CM1.AddConstraint(c1Copy);
            Assert.AreEqual(CM0.GetHashCode(), CM1.GetHashCode());

            Assert.IsTrue(CM0.Equals(CM1));
        }

        [Test()]
        public void ShouldBeDifferent()
        {
            var builder = new SimpleExprBuilder(true);

            var dummyV = SymbooglixLibTests.MapProxyTests.GetVariable("dummy", BPLType.Int);
            // Hack
            dummyV.SetMetadata((int)Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(dummyV));
            var v = new SymbolicVariable("foo", dummyV);
            var id = builder.Identifier(v);

            var c0 = new Constraint(builder.Gt(id, builder.ConstantInt(0)));
            var c1 = new Constraint(builder.Lt(id, builder.ConstantInt(0)));

            var CM0 = new ConstraintManager();
            var CM1 = new ConstraintManager();
            CM0.AddConstraint(c0);
            CM1.AddConstraint(c1);
            Assert.AreNotEqual(CM0.GetHashCode(), CM1.GetHashCode());
            Assert.IsFalse(CM0.Equals(CM1));
        }

        [Test()]
        public void GetSubSet()
        {
            var builder = new SimpleExprBuilder(true);

            var dummyV = SymbooglixLibTests.MapProxyTests.GetVariable("dummy", BPLType.Int);
            // Hack
            dummyV.SetMetadata((int)Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, new ProgramLocation(dummyV));
            var v = new SymbolicVariable("foo", dummyV);
            var id = builder.Identifier(v);

            var c0 = new Constraint(builder.Gt(id, builder.ConstantInt(0)));
            var c1 = new Constraint(builder.Lt(id, builder.ConstantInt(10)));

            var CM0 = new ConstraintManager();
            var CMSubset = new ConstraintManager();

            CM0.AddConstraint(c0);
            CM0.AddConstraint(c1);

            CMSubset.AddConstraint(c1);

            var getSubset = CM0.GetSubSet(new HashSet<Constraint>() { c1 });

            // Check they are the same
            Assert.AreEqual(1, getSubset.Count);
            Assert.AreEqual(1, CMSubset.Count);
            Assert.AreEqual(CMSubset.GetHashCode(), getSubset.GetHashCode());
            Assert.IsTrue(CMSubset.Equals(getSubset));
        }
    }
}

