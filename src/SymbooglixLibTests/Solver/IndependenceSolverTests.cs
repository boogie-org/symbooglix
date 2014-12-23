using NUnit.Framework;
using System;
using Symbooglix;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Linq;

namespace SolverTests
{
    [TestFixture()]
    public class IndependenceSolverTests
    {
        class MockSolver : Symbooglix.Solver.ISolverImpl
        {
            public List<Constraint> Constraints = new List<Constraint>();
            public Expr QueryExpr = null;
            public void SetConstraints(IConstraintManager constraints)
            {
                // Record the constraints we receive
                foreach (var c in constraints.Constraints)
                    Constraints.Add(c);
            }

            public Tuple<Symbooglix.Solver.Result, Symbooglix.Solver.IAssignment> ComputeSatisfiability(Expr queryExpr, bool computeAssignment)
            {
                // Record what the QueryExpr was
                QueryExpr = queryExpr;
                return new Tuple<Symbooglix.Solver.Result, Symbooglix.Solver.IAssignment>(Symbooglix.Solver.Result.SAT, null);
            }

            public void SetTimeout(int seconds)
            {
                throw new NotImplementedException();
            }

            public void Dispose()
            {

            }

            public Symbooglix.Solver.ISolverImplStatistics Statistics
            {
                get
                {
                    throw new NotImplementedException();
                }
            }
        }

        [Test()]
        public void RemoveNoConstraintsBasedOnVars()
        {
            IConstraintManager CM = new ConstraintManager();
            IExprBuilder builder = new ExprBuilder();

            // Dummy Boogie variable
            var bv8TypeIdent = new TypedIdent(Token.NoToken, "bv8", Microsoft.Boogie.Type.GetBvType(8));
            var dummyVarBv = new GlobalVariable(Token.NoToken, bv8TypeIdent);

            // dummyVar needs a programLocation, otherwise SymbolicVariable constructor raises an exception
            var progLoc = new ProgramLocation(dummyVarBv);
            dummyVarBv.SetMetadata<ProgramLocation>( (int) Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, progLoc);

            var s0 = new SymbolicVariable("s0", dummyVarBv).Expr;
            var s1 = new SymbolicVariable("s1", dummyVarBv).Expr;
            var s2 = new SymbolicVariable("s2", dummyVarBv).Expr;

            // Construct some constraints
            Expr c0 = builder.Eq(builder.BVAND(s0, s1), builder.ConstantBV(0, 8));
            Expr c1 = builder.Eq(s2, builder.ConstantBV(1, 8));

            CM.AddConstraint(c0, progLoc);
            CM.AddConstraint(c1, progLoc);

            var mockSolver = new MockSolver();
            var indepenceSolver = new Symbooglix.Solver.ConstraintIndependenceSolver(mockSolver);
            indepenceSolver.SetConstraints(CM);

            Expr queryExpr = builder.Eq(builder.BVAND(s1, s2), builder.ConstantBV(0, 8));

            indepenceSolver.ComputeSatisfiability(queryExpr, false);

            // Check no constraints were removed
            Assert.AreEqual(2, mockSolver.Constraints.Count);
            Assert.AreSame(queryExpr, mockSolver.QueryExpr);

            bool c0Found = false;
            bool c1Found = false;
            foreach (var constraint in mockSolver.Constraints)
            {
                if (c0 == constraint.Condition)
                    c0Found = true;

                if (c1 == constraint.Condition)
                    c1Found = true;
            }

            Assert.IsTrue(c0Found);
            Assert.IsTrue(c1Found);
        }

        [Test()]
        public void RemoveOneConstraintBasedOnVars()
        {
            IConstraintManager CM = new ConstraintManager();
            IExprBuilder builder = new ExprBuilder();

            // Dummy Boogie variable
            var bv8TypeIdent = new TypedIdent(Token.NoToken, "bv8", Microsoft.Boogie.Type.GetBvType(8));
            var dummyVarBv = new GlobalVariable(Token.NoToken, bv8TypeIdent);

            // dummyVar needs a programLocation, otherwise SymbolicVariable constructor raises an exception
            var progLoc = new ProgramLocation(dummyVarBv);
            dummyVarBv.SetMetadata<ProgramLocation>( (int) Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, progLoc);

            var s0 = new SymbolicVariable("s0", dummyVarBv).Expr;
            var s1 = new SymbolicVariable("s1", dummyVarBv).Expr;
            var s2 = new SymbolicVariable("s2", dummyVarBv).Expr;

            // Construct some constraints
            Expr c0 = builder.Eq(builder.BVAND(s0, s1), builder.ConstantBV(0, 8));
            Expr c1 = builder.Eq(s2, builder.ConstantBV(1, 8));

            CM.AddConstraint(c0, progLoc);
            CM.AddConstraint(c1, progLoc);

            var mockSolver = new MockSolver();
            var indepenceSolver = new Symbooglix.Solver.ConstraintIndependenceSolver(mockSolver);
            indepenceSolver.SetConstraints(CM);

            Expr queryExpr = builder.Eq(s1, builder.ConstantBV(0, 8));

            indepenceSolver.ComputeSatisfiability(queryExpr, false);

            // Check one constraint was removed
            Assert.AreEqual(1, mockSolver.Constraints.Count);
            Assert.AreSame(queryExpr, mockSolver.QueryExpr);

            var singleConstraint = mockSolver.Constraints.First();
            Assert.AreEqual(c0, singleConstraint.Condition);
        }

        [Test()]
        public void RemoveNoConstraintsBasedOnVarsAndFunctions()
        {
            IConstraintManager CM = new ConstraintManager();
            ExprBuilder builder = new ExprBuilder(); // FIXME: We depend on CreateFunctionCall()

            // Dummy Boogie variable
            var bv8Type = Microsoft.Boogie.Type.GetBvType(8);
            var bv8TypeIdent = new TypedIdent(Token.NoToken, "bv8", bv8Type);
            var dummyVarBv = new GlobalVariable(Token.NoToken, bv8TypeIdent);

            // dummyVar needs a programLocation, otherwise SymbolicVariable constructor raises an exception
            var progLoc = new ProgramLocation(dummyVarBv);
            dummyVarBv.SetMetadata<ProgramLocation>( (int) Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, progLoc);

            var s0 = new SymbolicVariable("s0", dummyVarBv).Expr;
            var s1 = new SymbolicVariable("s1", dummyVarBv).Expr;
            var s2 = new SymbolicVariable("s2", dummyVarBv).Expr;

            // Construct some constraints
            Expr c0 = builder.Eq(builder.BVAND(s0, s1), builder.ConstantBV(0, 8));
            Expr c1 = builder.Eq(s2, builder.ConstantBV(1, 8));

            var UFC = builder.CreateFunctionCall("foobar", Microsoft.Boogie.Type.Bool, new List<Microsoft.Boogie.Type>() { bv8Type });
            // foobar(0bv8) == 0bv8
            Expr c2 = builder.Eq(new NAryExpr(Token.NoToken, UFC, new List<Expr>() { builder.ConstantBV(0,8) }), builder.ConstantBV(0, 8));

            CM.AddConstraint(c0, progLoc);
            CM.AddConstraint(c1, progLoc);
            CM.AddConstraint(c2, progLoc);

            var mockSolver = new MockSolver();
            var indepenceSolver = new Symbooglix.Solver.ConstraintIndependenceSolver(mockSolver);
            indepenceSolver.SetConstraints(CM);

            // The query expression uses the "foobar" function so we need to keep constraints on that function
            Expr queryExpr = builder.And( builder.Eq(builder.BVAND(s1, s2), builder.ConstantBV(0, 8)), 
                                          new NAryExpr(Token.NoToken, UFC, new List<Expr>() { s1})
                              );

            indepenceSolver.ComputeSatisfiability(queryExpr, false);

            // Check no constraints were removed
            Assert.AreEqual(3, mockSolver.Constraints.Count);
            Assert.AreSame(queryExpr, mockSolver.QueryExpr);

            bool c0Found = false;
            bool c1Found = false;
            bool c2Found = false;
            foreach (var constraint in mockSolver.Constraints)
            {
                if (c0 == constraint.Condition)
                    c0Found = true;

                if (c1 == constraint.Condition)
                    c1Found = true;

                if (c2 == constraint.Condition)
                    c2Found = true;
            }

            Assert.IsTrue(c0Found);
            Assert.IsTrue(c1Found);
            Assert.IsTrue(c2Found);
        }

        [Test()]
        public void RemoveOneConstraintBasedOnVarsAndFunctions()
        {
            IConstraintManager CM = new ConstraintManager();
            ExprBuilder builder = new ExprBuilder(); // FIXME: We depend on CreateFunctionCall()

            // Dummy Boogie variable
            var bv8Type = Microsoft.Boogie.Type.GetBvType(8);
            var bv8TypeIdent = new TypedIdent(Token.NoToken, "bv8", bv8Type);
            var dummyVarBv = new GlobalVariable(Token.NoToken, bv8TypeIdent);

            // dummyVar needs a programLocation, otherwise SymbolicVariable constructor raises an exception
            var progLoc = new ProgramLocation(dummyVarBv);
            dummyVarBv.SetMetadata<ProgramLocation>( (int) Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, progLoc);

            var s0 = new SymbolicVariable("s0", dummyVarBv).Expr;
            var s1 = new SymbolicVariable("s1", dummyVarBv).Expr;
            var s2 = new SymbolicVariable("s2", dummyVarBv).Expr;

            // Construct some constraints
            Expr c0 = builder.Eq(builder.BVAND(s0, s1), builder.ConstantBV(0, 8));
            Expr c1 = builder.Eq(s2, builder.ConstantBV(1, 8));

            var UFC = builder.CreateFunctionCall("foobar", Microsoft.Boogie.Type.Bool, new List<Microsoft.Boogie.Type>() { bv8Type });
            // foobar(0bv8) == 0bv8
            Expr c2 = builder.Eq(new NAryExpr(Token.NoToken, UFC, new List<Expr>() { builder.ConstantBV(0,8) }), builder.ConstantBV(0, 8));

            CM.AddConstraint(c0, progLoc);
            CM.AddConstraint(c1, progLoc);
            CM.AddConstraint(c2, progLoc);

            var mockSolver = new MockSolver();
            var indepenceSolver = new Symbooglix.Solver.ConstraintIndependenceSolver(mockSolver);
            indepenceSolver.SetConstraints(CM);

            // The query expression does not use the "foobar" function so we don't need to keep constraints on that function
            Expr queryExpr = builder.Eq(builder.BVAND(s1, s2), builder.ConstantBV(0, 8));


            indepenceSolver.ComputeSatisfiability(queryExpr, false);

            // Check no constraints were removed
            Assert.AreEqual(2, mockSolver.Constraints.Count);
            Assert.AreSame(queryExpr, mockSolver.QueryExpr);

            bool c0Found = false;
            bool c1Found = false;
            foreach (var constraint in mockSolver.Constraints)
            {
                if (c0 == constraint.Condition)
                    c0Found = true;

                if (c1 == constraint.Condition)
                    c1Found = true;


            }

            Assert.IsTrue(c0Found);
            Assert.IsTrue(c1Found);
        }
    }
}

