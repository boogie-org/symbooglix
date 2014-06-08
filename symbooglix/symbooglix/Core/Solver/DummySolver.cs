using System;
using Microsoft.Boogie;
using Microsoft.Basetypes;

namespace symbooglix
{   
    namespace Solver
    {
        /// <summary>
        /// This solver considers every query to be satisfiable and gives
        /// the same assignment for everything.
        /// 
        /// It is meant for testing only.
        /// </summary>
        public class DummySolver : ISolver
        {
            public DummySolver()
            {
            }

            public void SetConstraints (ConstraintManager cm)
            {
                // The dummy solver doesn't care about these 
            }

            public void SetFunctions (System.Collections.Generic.IEnumerable<Microsoft.Boogie.Function> functions)
            {
                // The dummy solver doesn't care about these 
            }

            public Result IsQuerySat (Microsoft.Boogie.Expr Query, out IAssignment assignment)
            {
                assignment = new DummyAssignment(0);
                return Result.SAT;
            }

            public Result IsNotQuerySat (Microsoft.Boogie.Expr Query, out IAssignment assignment)
            {
                assignment = new DummyAssignment(0);
                return Result.SAT;
            }

            private class DummyAssignment : IAssignment
            {
                private int defaultValue;
                public DummyAssignment(int defaultValue)
                {
                    this.defaultValue = defaultValue;
                }

                public Microsoft.Boogie.LiteralExpr GetAssignment (SymbolicVariable SV)
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

