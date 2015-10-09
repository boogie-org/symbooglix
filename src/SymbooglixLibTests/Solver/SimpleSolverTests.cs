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
using Symbooglix;
using Solver = Symbooglix.Solver;
using NUnit.Framework;
using Microsoft.Boogie;

namespace SolverTests
{
    [TestFixture()]
    public class SimpleSolverTests
    {
        protected IExprBuilder GetBuilder()
        {
            return new SimpleExprBuilder(/*immutable*/ true);
        }

        protected Solver.ISolverImpl GetSolverImpl()
        {
            // FIXME: THIS IS A HACK
            var solver = SymbooglixLibTests.SymbooglixTest.GetSolver();
            return solver.SolverImpl;
        }

        protected IConstraintManager GetConstraintManager()
        {
            return new ConstraintManager();
        }

        SymbolicVariable GetVar(string name)
        {
            // FIXME: THIS IS A HACK!

            // Dummy Boogie variable
            var IntTypeIdent = new TypedIdent(Token.NoToken, name, Microsoft.Boogie.Type.Int);
            var dummyVarBv = new GlobalVariable(Token.NoToken, IntTypeIdent);

            // dummyVar needs a programLocation, otherwise SymbolicVariable constructor raises an exception
            var progLoc = new ProgramLocation(dummyVarBv);
            dummyVarBv.SetMetadata<ProgramLocation>( (int) Symbooglix.Annotation.AnnotationIndex.PROGRAM_LOCATION, progLoc);

            return new SymbolicVariable(name, dummyVarBv);
        }

        [TestCase(true, Solver.Result.SAT, Solver.Result.UNSAT)]
        [TestCase(false, Solver.Result.UNSAT, Solver.Result.SAT)]
        public void branchFeasibilityTrivialQueryExpr(bool trueBranch, Solver.Result expectedTrueBranch, Solver.Result expectedFalseBranch)
        {
            var builder = GetBuilder();
            var solver = new Solver.SimpleSolver(GetSolverImpl());
            var xVar = GetVar("x");

            var constraint0Expr = builder.Lt(xVar.Expr, builder.ConstantInt(0));
            var constraint0 = new Constraint(constraint0Expr);
            var cm = GetConstraintManager();
            cm.AddConstraint(constraint0);

            var result = solver.CheckBranchSatisfiability(cm, new Constraint(builder.ConstantBool(trueBranch)), builder);
            Assert.AreEqual(expectedTrueBranch, result.TrueBranch);
            Assert.AreEqual(expectedFalseBranch, result.FalseBranch);
        }

        [Test()]
        public void branchFeasibilityNonTrivialOnlyTrueBranch()
        {
            var builder = GetBuilder();
            var solver = new Solver.SimpleSolver(GetSolverImpl());
            var xVar = GetVar("x");

            var constraint0Expr = builder.Lt(xVar.Expr, builder.ConstantInt(0));
            var constraint0 = new Constraint(constraint0Expr);
            var cm = GetConstraintManager();
            cm.AddConstraint(constraint0);

            var queryExpr = builder.Lt(xVar.Expr, builder.ConstantInt(1));

            var result = solver.CheckBranchSatisfiability(cm, new Constraint(queryExpr), builder);
            Assert.AreEqual(Solver.Result.SAT, result.TrueBranch);
            Assert.AreEqual(Solver.Result.UNSAT, result.FalseBranch);
        }

        [Test()]
        public void branchFeasibilityNonTrivialOnlyFalseBranch()
        {
            var builder = GetBuilder();
            var solver = new Solver.SimpleSolver(GetSolverImpl());
            var xVar = GetVar("x");

            var constraint0Expr = builder.Lt(xVar.Expr, builder.ConstantInt(0));
            var constraint0 = new Constraint(constraint0Expr);
            var cm = GetConstraintManager();
            cm.AddConstraint(constraint0);

            var queryExpr = builder.Gt(xVar.Expr, builder.ConstantInt(1));

            var result = solver.CheckBranchSatisfiability(cm, new Constraint(queryExpr), builder);
            Assert.AreEqual(Solver.Result.UNSAT, result.TrueBranch);
            Assert.AreEqual(Solver.Result.SAT, result.FalseBranch);
        }

        [Test()]
        public void branchFeasibilityNonTrivialBothBranches()
        {
            var builder = GetBuilder();
            var solver = new Solver.SimpleSolver(GetSolverImpl());
            var xVar = GetVar("x");

            var constraint0Expr = builder.Lt(xVar.Expr, builder.ConstantInt(0));
            var constraint0 = new Constraint(constraint0Expr);
            var cm = GetConstraintManager();
            cm.AddConstraint(constraint0);

            var queryExpr = builder.Lt(xVar.Expr, builder.ConstantInt(-1));

            var result = solver.CheckBranchSatisfiability(cm, new Constraint(queryExpr), builder);
            Assert.AreEqual(Solver.Result.SAT, result.TrueBranch);
            Assert.AreEqual(Solver.Result.SAT, result.FalseBranch);
        }
    }
}

