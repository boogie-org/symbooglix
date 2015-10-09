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
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace Symbooglix
{   
    namespace Solver
    {
        /// <summary>
        /// This solver considers every query to "resultIsAlways"
        /// with the same assignment for everything.
        /// 
        /// It is meant for testing only.
        /// </summary>
        public class DummySolver : ISolverImpl
        {
            private Result ResultIsAlways;

            public DummySolver(Solver.Result resultIsAlways = Result.SAT)
            {
                this.ResultIsAlways = resultIsAlways;
            }

            public void SetTimeout(int seconds)
            {
                // The dummy solver doesn't care about this
            }
            public void Interrupt()
            {
                // Dummy solver doesn't need to do anything
            }

            class DummySolverResult : IQueryResult
            {
                private DummyAssignment Assignment;
                public DummySolverResult(Result r, int defaultValue)
                {
                    this.Satisfiability = r;
                    Assignment = new DummyAssignment(defaultValue);
                }

                public IAssignment GetAssignment()
                {
                    return Assignment;
                }

                public IUnsatCore GetUnsatCore()
                {
                    throw new NotImplementedException();
                }

                public Result Satisfiability
                {
                    get;
                    private set;
                }
            }

            public IQueryResult ComputeSatisfiability(Query query)
            {
                // Dummy Solver thinks everything is "ResultIsAlways"
                return new DummySolverResult(ResultIsAlways, 0);
            }

            public void Dispose()
            {
                // Dummy solver doesn't need to clean up anything
                return;
            }

            public ISolverImplStatistics Statistics
            {
                get
                {
                    return new DummyStatistics();
                }
            }
                
            private class DummyAssignment : IAssignment
            {
                private int defaultValue;
                public DummyAssignment(int defaultValue)
                {
                    this.defaultValue = defaultValue;
                }

                public Microsoft.Boogie.LiteralExpr GetAssignment(SymbolicVariable SV)
                {
                    if (SV.TypedIdent.Type.IsBv)
                    {
                        int width = SV.TypedIdent.Type.BvBits;
                        return new LiteralExpr(Token.NoToken, BigNum.FromInt(defaultValue), width);
                    }
                    else if (SV.TypedIdent.Type.IsBool)
                    {
                        return defaultValue > 0 ? Expr.True : Expr.False;
                    }
                    else if (SV.TypedIdent.Type.IsInt)
                    {
                        return new LiteralExpr(Token.NoToken, BigNum.FromInt(defaultValue));
                    }
                    else if (SV.TypedIdent.Type.IsReal)
                    {
                        return new LiteralExpr(Token.NoToken, BigDec.FromInt(defaultValue));
                    }
                    else
                    {
                        throw new NotImplementedException();
                    }
                }
            }
        }

        public class DummyStatistics : ISolverImplStatistics
        {
            public void Reset()
            {
                return;
            }

            public void WriteAsYAML(System.CodeDom.Compiler.IndentedTextWriter TW)
            {
                TW.WriteLine("null");
            }
        }
    }
}

