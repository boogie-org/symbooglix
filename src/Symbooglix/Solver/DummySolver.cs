using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace Symbooglix
{   
    namespace Solver
    {
        /// <summary>
        /// This solver considers every query to be satisfiable and gives
        /// the same assignment for everything.
        /// 
        /// It is meant for testing only.
        /// </summary>
        public class DummySolver : ISolverImpl
        {
            public DummySolver()
            {
            }

            public void SetConstraints(ConstraintManager cm)
            {
                // The dummy solver doesn't care about these 
            }

            public void SetTimeout(int seconds)
            {
                // The dummy solver doesn't care about this
            }

            public Tuple<Result, IAssignment> ComputeSatisfiability(Expr queryExpr, bool computeAssignment)
            {
                // Dummy Solver thinks everything is satisfiable
                if (computeAssignment)
                    return Tuple.Create(Result.SAT, new DummyAssignment(0) as IAssignment);
                else
                    return Tuple.Create(Result.SAT, null as IAssignment);
            }

            public void Dispose()
            {
                // Dummy solver doesn't need to clean up anything
                return;
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



    }
}

