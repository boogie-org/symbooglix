using System;
using Microsoft.Boogie;
using System.IO;
using System.CodeDom.Compiler;
using System.Collections.Generic;

namespace symbooglix
{
    public class SMTLIBQueryPrinter : Traverser
    {
        private ExprSMTLIBPrinter P = null;
        private HashSet<SymbolicVariable> symbolicsToDeclare = null;
        private HashSet<Microsoft.Boogie.Function> functionsToDeclare = null;

        public SMTLIBQueryPrinter(TextWriter TW, bool humanReadable = true) : base(new ExprSMTLIBPrinter(TW, humanReadable))
        {
            // Do the cast once so we don't need to keep doing it
            P = this.Visitor as ExprSMTLIBPrinter;

            symbolicsToDeclare = new HashSet<SymbolicVariable>();
            functionsToDeclare = new HashSet<Function>();
        }

        public void clearDeclarations()
        {
            symbolicsToDeclare.Clear();
            functionsToDeclare.Clear();
        }

        public void addDeclarations(Expr e)
        {
            // TODO
        }

        public enum Logic
        {
            QF_BV,
            QF_ABV,
            Q_ALL
        }

        public void printSetLogic(Logic L)
        {
            P.TW.WriteLine("(set-logic " + L.ToString() + " )");
        }

        public void printAssert(Expr e)
        {
            P.TW.Write("(assert");
            P.pushIndent();
            Traverse(e);
            P.popIndent();
            P.TW.WriteLine(")");
        }

        public void printCheckSat()
        {
            P.TW.WriteLine("(check-sat)");
        }

        public void printExit()
        {
            P.TW.WriteLine("(exit)");
        }

        public void printSetOption(string option)
        {
            P.TW.WriteLine("(set-option :" + option + ")");
        }


        /// <summary>
        /// Print the expression to the TextWriter in
        /// SMT-LIB format. This does not include an
        /// enclosing (assert <Expr>) so it should probably
        /// not be used directly
        /// </summary>
        /// <param name="root">Expr to print</param>
        public override Expr Traverse(Expr root)
        {
            // This Traversal is recursive
            return Visit(root);
        }

        // This class handles printing of Expr
        private class ExprSMTLIBPrinter : IExprVisitor
        {
            public TextWriter TW = null;
            public bool humanReadable;
            private int indent = 4;
            public ExprSMTLIBPrinter(TextWriter TW, bool humanReadable)
            {
                this.humanReadable = humanReadable;
                if (humanReadable)
                {
                    this.TW = new IndentedTextWriter(TW);
                    // don't modify the indent here.
                }
                else
                    this.TW = TW;
            }

            public void pushIndent()
            {
                if (humanReadable)
                {
                    ( this.TW as IndentedTextWriter ).Indent += this.indent;
                    TW.Write(TW.NewLine);
                }
                else
                {
                    TW.Write(" ");
                }
            }

            public void popIndent()
            {
                if (humanReadable)
                {
                    ( this.TW as IndentedTextWriter ).Indent -= this.indent;
                    TW.Write(TW.NewLine);
                }
                else
                {
                    TW.Write(" ");
                }
            }

            public Expr VisitLiteralExpr(LiteralExpr e)
            {
                if (e.isBool)
                {
                    if (e.IsTrue)
                        TW.Write("true");
                    else
                        TW.Write("false");
                }
                else if (e.isBvConst)
                {
                    // FIXME: Support other bit vector literal printing modes
                    TW.Write(string.Format("(_ bv{0} {1})", e.asBvConst.Value, e.asBvConst.Bits));
                }
                else if (e.isBigNum)
                {
                    TW.Write(e.asBigNum);
                }
                else
                {
                    throw new NotImplementedException("LiteralExpr type not handled");
                }

                return e;
            }

            public Expr VisitIdentifierExpr (IdentifierExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitOldExpr (OldExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitCodeExpr (CodeExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitBvExtractExpr (BvExtractExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitBvConcatExpr (BvConcatExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitForallExpr (ForallExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitExistExpr (ExistsExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitLambdaExpr (LambdaExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitNot (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitNeg (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitAdd (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitSub (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitMul (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitDiv (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitMod (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitRealDiv (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitEq (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitNeq (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitGt (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitGe (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitLt (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitLe (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitAnd (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitOr (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitImp (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitIff (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitSubType (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitMapStore (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitMapSelect (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitIfThenElse (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitFunctionCall (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitTypeCoercion (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr VisitArithmeticCoercion (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvadd (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvsub (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvmul (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvudiv (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvurem (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvsdiv (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvsrem (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvsmod (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_sign_extend (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_zero_extend (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvneg (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvand (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvor (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvnot (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvxor (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvshl (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvlshr (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvashr (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvult (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvule (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvugt (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvuge (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvslt (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvsle (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvsgt (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

            public Expr Visit_bvsge (NAryExpr e)
            {
                throw new NotImplementedException ();
            }

        }

    }
}

