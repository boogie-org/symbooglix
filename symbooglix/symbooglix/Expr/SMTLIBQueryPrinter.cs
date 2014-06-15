using System;
using Microsoft.Boogie;
using System.IO;
using System.CodeDom.Compiler;
using System.Collections.Generic;
using System.Diagnostics;

namespace symbooglix
{
    public class SMTLIBQueryPrinter : Traverser
    {
        private ExprSMTLIBPrinter P = null;
        private HashSet<SymbolicVariable> symbolicsToDeclare = null;
        private HashSet<Microsoft.Boogie.Function> functionsToDeclare = null;
        private FindSymbolicsVisitor FSV = null;

        public SMTLIBQueryPrinter(TextWriter TW, bool humanReadable = true) : base(null)
        {
            this.Visitor = new ExprSMTLIBPrinter(TW, this, humanReadable);

            // Do the cast once so we don't need to keep doing it
            P = this.Visitor as ExprSMTLIBPrinter;

            symbolicsToDeclare = new HashSet<SymbolicVariable>();
            functionsToDeclare = new HashSet<Function>();
            FSV = new FindSymbolicsVisitor(symbolicsToDeclare); // Have the visitor use our container
        }

        public void clearDeclarations()
        {
            symbolicsToDeclare.Clear();
            functionsToDeclare.Clear();
        }

        public void addDeclarations(Expr e)
        {
            FSV.Visit(e);
            // TODO Add FindFunctionsVisitor
        }

        public enum Logic
        {
            QF_BV,
            QF_ABV,
            Q_ALL
        }

        public void printVariableDeclarations()
        {
            if (P.humanReadable)
                printCommentLine("Start variable declarations");

            foreach (var symbolic in symbolicsToDeclare)
            {
                P.TW.Write("(declare-fun " + symbolic.Name + " () " + getSMTLIBType(symbolic.TypedIdent.Type));
                P.TW.Write(")");

                if (P.humanReadable)
                    printCommentLine("Origin: " + symbolic.Origin, false);

                P.TW.Write(P.TW.NewLine);
            }

            if (P.humanReadable)
                printCommentLine("End variable declarations");
        }

        public void printFunctionDeclarations()
        {
            // TODO
        }

        public void printCommentLine(string comment, bool AddEndOfLineCharacter = true)
        {
            if (P.humanReadable)
            {
                P.TW.Write("; " + comment);

                if (AddEndOfLineCharacter)
                    P.TW.WriteLine("");
            }
        }

        public static string getSMTLIBType(Microsoft.Boogie.Type T)
        {
            if (T is BvType)
            {
                var BVT = T as BvType;
                return "(_ BitVec " + BVT.Bits + ")";
            }
            else if (T is BasicType)
            {
                var ST = ( T as BasicType ).T;
                switch (ST)
                {
                    case SimpleType.Bool:
                        return "(Bool)";
                    case SimpleType.Int:
                        return "(Int)";
                    case SimpleType.Real:
                        return "(Real)";
                    default:
                        throw new NotImplementedException("Unsupported SimpleType " + ST.ToString());
                }
            }
            else if (T is MapType)
            {
                var MT = T as MapType;
                // FIXME: How do I interpret Arguments of a map type
                throw new NotImplementedException("MapType (" + MT.ToString() + ") not supported yet");
            }
            else
            {
                throw new NotImplementedException("The type " + T.ToString() + " is not supported");
            }
        }

        public void printSetLogic(Logic L)
        {
            P.TW.WriteLine("(set-logic " + L.ToString() + " )");
        }

        public void printAssert(Expr e)
        {
            P.TW.Write("(assert");
            P.pushIndent();
            P.printSeperator();
            Visit(e);
            P.popIndent();
            P.printSeperator();
            P.TW.WriteLine(")");
        }

        public void printCheckSat()
        {
            P.TW.WriteLine("(check-sat)");
            P.TW.Flush();
        }

        public void printExit()
        {
            P.TW.WriteLine("(exit)");
            P.TW.Flush();
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
            private int indent = 2;
            public SMTLIBQueryPrinter SQP = null;
            public ExprSMTLIBPrinter(TextWriter TW, SMTLIBQueryPrinter SQP ,bool humanReadable)
            {
                this.SQP = SQP;
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
                    var IDT = this.TW as IndentedTextWriter;
                    IDT.Indent += this.indent;
                }
            }

            public void printSeperator()
            {
                if (humanReadable)
                    TW.WriteLine("");
                else
                    TW.Write(" ");
            }

            public void popIndent()
            {
                if (humanReadable)
                {
                    var IDT = this.TW as IndentedTextWriter;
                    IDT.Indent -= this.indent;
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
                if (!( e.Decl is SymbolicVariable ))
                    throw new InvalidDataException("non symbolic found in Expr"); //FIXME: Add our own Expr types

                TW.Write(e.Name);
                return e;
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
                // SMTLIBv2 semantics
                // ((_ extract i j) (_ BitVec m) (_ BitVec n))
                // - extraction of bits i down to j from a bitvector of size m to yield a
                // new bitvector of size n, where n = i - j + 1

                // Boogie semantics
                // ABitVector[<end>:<start>]
                // This operation selects bits starting at <start> to <end> but not including <end>
                Debug.Assert(( e.End - 1 ) >= ( e.Start ), "Wrong extract bits for BvExtractExpr");
                TW.Write("((_ extract " + (e.End -1) + " " + e.Start + ")");
                pushIndent();
                printSeperator();
                SQP.Visit(e.Bitvector);
                popIndent();
                printSeperator();
                TW.Write(")");
                return e;
            }

            public Expr VisitBvConcatExpr (BvConcatExpr e)
            {
                TW.Write("(concat");
                pushIndent();
                printSeperator();
                SQP.Visit(e.E0);
                printSeperator();
                SQP.Visit(e.E1);
                popIndent();
                printSeperator();
                TW.Write(")");
                return e;
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

            public Expr VisitNot(NAryExpr e)
            {
                return printUnaryOperator("not", e);
            }

            public Expr VisitNeg (NAryExpr e)
            {
                return printUnaryOperator("-", e);
            }

            public Expr VisitAdd (NAryExpr e)
            {
                return printBinaryOperator("+", e);
            }

            public Expr VisitSub (NAryExpr e)
            {
                return printBinaryOperator("-", e);
            }

            public Expr VisitMul (NAryExpr e)
            {
                return printBinaryOperator("*", e);
            }

            public Expr VisitDiv (NAryExpr e)
            {
                Debug.Assert(( e.Args[0] as Expr ).Type.IsInt && ( e.Args[1] as Expr ).Type.IsInt, "wrong types given to div!");
                return printBinaryOperator("div", e);
            }

            public Expr VisitMod (NAryExpr e)
            {
                return printBinaryOperator("mod", e);
            }

            public Expr VisitRealDiv (NAryExpr e)
            {
                Debug.Assert(( e.Args[0] as Expr ).Type.IsReal && ( e.Args[1] as Expr ).Type.IsReal, "wrong types given to div!");
                return printBinaryOperator("/", e);
            }

            public Expr VisitEq (NAryExpr e)
            {
                return printBinaryOperator("=", e);
            }

            public Expr VisitNeq (NAryExpr e)
            {
                // There isn't a != operator in SMTLIBv2 so construct the equivalent
                Expr temp = Expr.Not(Expr.Eq(e.Args[0], e.Args[1]));
                SQP.Visit(temp);
                return e;
            }

            public Expr VisitGt (NAryExpr e)
            {
                return printBinaryOperator(">", e);
            }

            public Expr VisitGe (NAryExpr e)
            {
                return printBinaryOperator(">=", e);
            }

            public Expr VisitLt (NAryExpr e)
            {
                return printBinaryOperator("<", e);
            }

            public Expr VisitLe (NAryExpr e)
            {
                return printBinaryOperator("<=", e);
            }

            public Expr VisitAnd (NAryExpr e)
            {
                return printBinaryOperator("and", e);
            }

            public Expr VisitOr (NAryExpr e)
            {
                return printBinaryOperator("or", e);
            }

            public Expr VisitImp (NAryExpr e)
            {
                return printBinaryOperator("=>", e);
            }

            public Expr VisitIff (NAryExpr e)
            {
                // There is not <==> operator in SMTLIBv2 so construct its equivalent
                Expr temp = Expr.And(Expr.Imp(e.Args[0], e.Args[1]), Expr.Imp(e.Args[1], e.Args[0]));
                SQP.Visit(temp);
                return e;
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
                TW.Write("(ite");
                pushIndent();
                printSeperator();
                SQP.Visit(e.Args[0]);
                printSeperator();
                SQP.Visit(e.Args[1]);
                printSeperator();
                SQP.Visit(e.Args[2]);
                popIndent();
                printSeperator();
                TW.Write(")");
                return e;
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

            public Expr Visit_bvadd(NAryExpr e)
            {
                return printBinaryOperator("bvadd", e);
            }

            public Expr Visit_bvsub(NAryExpr e)
            {
                return printBinaryOperator("bvsub", e);
            }

            public Expr Visit_bvmul(NAryExpr e)
            {
                return printBinaryOperator("bvmul", e);
            }

            public Expr Visit_bvudiv (NAryExpr e)
            {
                return printBinaryOperator("bvudiv", e);
            }

            public Expr Visit_bvurem (NAryExpr e)
            {
                return printBinaryOperator("bvrem", e);
            }

            public Expr Visit_bvsdiv (NAryExpr e)
            {
                return printBinaryOperator("bvsdiv", e);
            }

            public Expr Visit_bvsrem (NAryExpr e)
            {
                return printBinaryOperator("bvsrem", e);
            }

            public Expr Visit_bvsmod (NAryExpr e)
            {
                return printBinaryOperator("bvsmod", e);
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
                return printBinaryOperator("bvneg", e);
            }

            public Expr Visit_bvand (NAryExpr e)
            {
                return printBinaryOperator("bvand", e);
            }

            public Expr Visit_bvor (NAryExpr e)
            {
                return printBinaryOperator("bvor", e);
            }

            public Expr Visit_bvnot (NAryExpr e)
            {
                return printUnaryOperator("bvnot", e);
            }

            public Expr Visit_bvxor (NAryExpr e)
            {
                return printBinaryOperator("bvxor", e);
            }

            public Expr Visit_bvshl (NAryExpr e)
            {
                return printBinaryOperator("bvshl", e);
            }

            public Expr Visit_bvlshr (NAryExpr e)
            {
                return printBinaryOperator("bvlshr", e);
            }

            public Expr Visit_bvashr (NAryExpr e)
            {
                return printBinaryOperator("bvashr", e);
            }

            public Expr Visit_bvult (NAryExpr e)
            {
                return printBinaryOperator("bvult", e);
            }

            public Expr Visit_bvule (NAryExpr e)
            {
                return printBinaryOperator("bvule", e);
            }

            public Expr Visit_bvugt (NAryExpr e)
            {
                return printBinaryOperator("bvugt", e);
            }

            public Expr Visit_bvuge (NAryExpr e)
            {
                return printBinaryOperator("bvuge", e);
            }

            public Expr Visit_bvslt (NAryExpr e)
            {
                return printBinaryOperator("bvslt", e);
            }

            public Expr Visit_bvsle (NAryExpr e)
            {
                return printBinaryOperator("bvsle", e);
            }

            public Expr Visit_bvsgt (NAryExpr e)
            {
                return printBinaryOperator("bvsgt", e);
            }

            public Expr Visit_bvsge (NAryExpr e)
            {
                return printBinaryOperator("bvsge", e);
            }

            // We go to a lot of effort in the Traverser to read the
            // string bvbuiltin to call the right method in IExprVisitor
            // but then we delegate back a single function for printing
            // binary operators using only the string name.
            // A bit inefficient...
            private Expr printBinaryOperator(string name, NAryExpr e)
            {
                Debug.Assert(e.Args.Count == 2, "Incorrect number of arguments");
                TW.Write("(" + name);
                pushIndent();
                printSeperator();
                SQP.Visit(e.Args[0]);
                printSeperator();
                SQP.Visit(e.Args[1]);
                popIndent();
                printSeperator();
                TW.Write(")");
                return e;
            }

            private Expr printUnaryOperator(string name, NAryExpr e)
            {
                Debug.Assert(e.Args.Count == 1, "Incorrect number of arguments");
                TW.Write("(" + name);
                pushIndent();
                printSeperator();
                SQP.Visit(e.Args[0]);
                popIndent();
                printSeperator();
                TW.Write(")");
                return e;
            }

        }

    }
}

