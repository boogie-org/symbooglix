using System;
using Microsoft.Boogie;
using System.IO;
using System.CodeDom.Compiler;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace symbooglix
{
    public class SMTLIBQueryPrinter : Traverser
    {
        private ExprSMTLIBPrinter P = null;
        private HashSet<SymbolicVariable> symbolicsToDeclare = null;
        private HashSet<Microsoft.Boogie.Function> functionsToDeclare = null;
        private FindSymbolicsVisitor FSV = null;
        private FindFunctionsVisitor FFV = null;

        public SMTLIBQueryPrinter(TextWriter TW, bool humanReadable = true) : base(null)
        {
            this.Visitor = new ExprSMTLIBPrinter(TW, this, humanReadable);

            // Do the cast once so we don't need to keep doing it
            P = this.Visitor as ExprSMTLIBPrinter;

            symbolicsToDeclare = new HashSet<SymbolicVariable>();
            functionsToDeclare = new HashSet<Function>();
            FSV = new FindSymbolicsVisitor(symbolicsToDeclare); // Have the visitor use our container
            FFV = new FindFunctionsVisitor(functionsToDeclare); // Have the visitor use our container
        }

        public void clearDeclarations()
        {
            symbolicsToDeclare.Clear();
            functionsToDeclare.Clear();
        }

        public void addDeclarations(Expr e)
        {
            FSV.Visit(e);
            FFV.Visit(e);
        }

        public enum Logic
        {
            QF_BV,
            QF_ABV,
            ALL_SUPPORTED // CVC4 specific
        }

        public void changeOutput(TextWriter newTW)
        {
            Debug.Assert(newTW != null, "New output cannot be null!");
            P.TW = newTW;
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
            if (P.humanReadable)
                printCommentLine("Start function declarations");

            foreach (var function in functionsToDeclare)
            {
                if (function.Body != null)
                    throw new NotSupportedException("Can't handle function bodies yet");

                P.TW.Write("(declare-fun " + function.Name + " (");
                foreach (var type in function.InParams.Select( x => x.TypedIdent.Type ))
                {
                    P.TW.Write(getSMTLIBType(type) + " ");
                }
                P.TW.Write(") ");

                if (function.OutParams.Count != 1)
                    throw new NotSupportedException("Only single parameters are supported!");

                P.TW.Write(getSMTLIBType(function.OutParams[0].TypedIdent.Type) + ")");
                P.TW.Write(P.TW.NewLine);
            }

            if (P.humanReadable)
                printCommentLine("End function declarations");
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
                        return "Bool";
                    case SimpleType.Int:
                        return "Int";
                    case SimpleType.Real:
                        return "Real";
                    default:
                        throw new NotImplementedException("Unsupported SimpleType " + ST.ToString());
                }
            }
            else if (T is MapType)
            {
                var MT = T as MapType;
                // We are using Z3's Native ArrayTheory (allows for Arrays of Arrays) here. I don't know if other Solvers support this.
                Debug.Assert(MT.Arguments.Count >= 1, "MapType has too few arguments");
                string mapTypeAsString = "";
                foreach (var domainType in MT.Arguments)
                {
                    mapTypeAsString += "(Array " + getSMTLIBType(domainType) + " ";
                }

                // Now print the final result from the map (the codomain)
                mapTypeAsString += getSMTLIBType(MT.Result) + " ";

                // Now add closing braces
                for (int index = 0; index < MT.Arguments.Count; ++index)
                {
                    mapTypeAsString += ")";
                }
                return mapTypeAsString;
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
                // Should we make this check better by recording what variables are currently bound?
                if (!( ( e.Decl is SymbolicVariable ) || (e.Decl is BoundVariable )))
                    throw new InvalidDataException("non symbolic/BoundVariable found in Expr"); //FIXME: Add our own Expr types

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

            public Expr VisitForallExpr(ForallExpr e)
            {
                return printQuantifierExpr(e);
            }

            public Expr VisitExistExpr(ExistsExpr e)
            {
                return printQuantifierExpr(e);
            }

            private Expr printQuantifierExpr(QuantifierExpr QE)
            {
                if (QE is ExistsExpr)
                    TW.Write("(exists");
                else if (QE is ForallExpr)
                    TW.Write("(forall");
                else
                    throw new NotSupportedException("Unsupported quantifier expr");

                pushIndent();
                printSeperator();
                TW.Write("(");
                pushIndent();
                printSeperator();

                foreach (var boundVar in QE.Dummies)
                {
                    printSeperator();
                    TW.Write("(" + boundVar.Name + " " + getSMTLIBType(boundVar.TypedIdent.Type) + ")");
                }
                popIndent();
                printSeperator();
                TW.Write(")");
                printSeperator();
                SQP.Visit(QE.Body);
                popIndent();
                printSeperator();
                TW.Write(")");
                return QE;
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

                // We can't use Expr.Not here because it rewrites  Expr.Not(Expr.Eq(e.Args[0], e.Args[1]))
                // into the same expr as "e" which will cause infinite recursion.
                Expr temp = Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Not, Expr.Eq(e.Args[0], e.Args[1]));
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

            public Expr VisitMapStore(NAryExpr e)
            {
                // FIXME: Can we assert that we match the SMT-LIB order of args?
                return printTernaryOperator("store", e);
            }

            public Expr VisitMapSelect(NAryExpr e)
            {
                return printBinaryOperator("select", e);
            }

            public Expr VisitIfThenElse (NAryExpr e)
            {
                return printTernaryOperator("ite", e);
            }

            public Expr VisitFunctionCall (NAryExpr e)
            {
                var FC = e.Fun as FunctionCall;
                TW.Write("(" + FC.Func.Name);
                pushIndent();
                printSeperator();
                foreach (var param in e.Args)
                {
                    SQP.Visit(param);
                    printSeperator(); // FIXME: There shouldn't be one on the last param
                }
                popIndent();
                printSeperator();
                TW.Write(")");
                return e;
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

            public Expr Visit_sign_extend(NAryExpr e)
            {
                return printSignExtend(e, "sign_extend");
            }

            public Expr Visit_zero_extend(NAryExpr e)
            {
                //  ((_ zero_extend i) (_ BitVec m) (_ BitVec m+i))
                // ((_ zero_extend i) x) means extend x with zeroes to the (unsigned)
                // equivalent bitvector of size m+i
                return printSignExtend(e, "zero_extend");
            }

            private Expr printSignExtend(NAryExpr e, string extensionType)
            {
                Debug.Assert(extensionType == "zero_extend" || extensionType == "sign_extend");
                Debug.Assert(e.Args.Count == 1);
                Debug.Assert(e.Args[0].Type.IsBv, "Not a bitvector!");
                Debug.Assert(e.Type.IsBv, "Out is not a bitvector!");

                // Work out extension amount
                int numberOfBitsToAdd = ( e.Type.BvBits - e.Args[0].Type.BvBits );
                Debug.Assert(numberOfBitsToAdd >= 0, "Number of bits to add calculation is incorrect"); // FIXME: Throw exception instead
                return printUnaryOperator("(_ " + extensionType + " " + numberOfBitsToAdd + ")", e);
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

            private Expr printTernaryOperator(string name, NAryExpr e)
            {
                Debug.Assert(e.Args.Count == 3, "Incorrect number of arguments");
                TW.Write("(" + name);
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

        }

    }
}

