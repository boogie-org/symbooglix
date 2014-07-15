using System;
using Microsoft.Boogie;
using System.IO;
using System.CodeDom.Compiler;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace Symbooglix
{
    public class SMTLIBQueryPrinter : IExprVisitor
    {
        private HashSet<SymbolicVariable> symbolicsToDeclare = null;
        private HashSet<Microsoft.Boogie.Function> functionsToDeclare = null;
        private FindSymbolicsVisitor FSV = null;
        private FindFunctionsVisitor FFV = null;
        private TextWriter TW = null;
        private Traverser TheTraverser = null;
        public bool HumanReadable;
        private int Indent;

        public SMTLIBQueryPrinter(TextWriter TW, bool humanReadable = true, int indent=2)
        {
            this.HumanReadable = humanReadable; // Must be set before output is set
            ChangeOutput(TW);
            this.Indent = indent;

            symbolicsToDeclare = new HashSet<SymbolicVariable>();
            functionsToDeclare = new HashSet<Function>();
            FSV = new FindSymbolicsVisitor(symbolicsToDeclare); // Have the visitor use our container
            FFV = new FindFunctionsVisitor(functionsToDeclare); // Have the visitor use our container

            TheTraverser = new SMTLIBTraverser(this);
        }

        private class SMTLIBTraverser : Traverser
        {

            public SMTLIBTraverser(IExprVisitor visitor) : base(visitor) {}

            public override Expr Traverse(Expr root)
            {
                return Visit(root);
            }
        }

        // Eurgh this level of indirection... This needs rethinking
        public void PrintExpr(Expr root)
        {
            TheTraverser.Traverse(root);
        }

        public void ClearDeclarations()
        {
            symbolicsToDeclare.Clear();
            functionsToDeclare.Clear();
        }

        public void AddDeclarations(Expr e)
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

        public void ChangeOutput(TextWriter newTW)
        {
            Debug.Assert(newTW != null, "New output cannot be null!");
            if (HumanReadable)
            {
                this.TW = new IndentedTextWriter(newTW);
            }
            else
                this.TW = newTW;
        }

        public void PrintVariableDeclarations()
        {
            if (HumanReadable)
                PrintCommentLine("Start variable declarations");

            foreach (var symbolic in symbolicsToDeclare)
            {
                TW.Write("(declare-fun " + symbolic.Name + " () " + GetSMTLIBType(symbolic.TypedIdent.Type));
                TW.Write(")");

                if (HumanReadable)
                    PrintCommentLine("Origin: " + symbolic.Origin, false);

                TW.Write(TW.NewLine);
            }

            if (HumanReadable)
                PrintCommentLine("End variable declarations");
        }

        public void PrintFunctionDeclarations()
        {
            if (HumanReadable)
                PrintCommentLine("Start function declarations");

            foreach (var function in functionsToDeclare)
            {
                if (function.Body != null)
                    throw new NotSupportedException("Can't handle function bodies yet");

                TW.Write("(declare-fun " + function.Name + " (");
                foreach (var type in function.InParams.Select( x => x.TypedIdent.Type ))
                {
                    TW.Write(GetSMTLIBType(type) + " ");
                }
                TW.Write(") ");

                if (function.OutParams.Count != 1)
                    throw new NotSupportedException("Only single parameters are supported!");

                TW.Write(GetSMTLIBType(function.OutParams[0].TypedIdent.Type) + ")");
                TW.Write(TW.NewLine);
            }

            if (HumanReadable)
                PrintCommentLine("End function declarations");
        }

        public void PrintCommentLine(string comment, bool AddEndOfLineCharacter = true)
        {
            if (HumanReadable)
            {
                TW.Write("; " + comment);

                if (AddEndOfLineCharacter)
                    TW.WriteLine("");
            }
        }

        public static string GetSMTLIBType(Microsoft.Boogie.Type T)
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
                    mapTypeAsString += "(Array " + GetSMTLIBType(domainType) + " ";
                }

                // Now print the final result from the map (the codomain)
                mapTypeAsString += GetSMTLIBType(MT.Result) + " ";

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

        public void PrintSetLogic(Logic L)
        {
            TW.WriteLine("(set-logic " + L.ToString() + " )");
        }

        public void PrintAssert(Expr e)
        {
            TW.Write("(assert");
            PushIndent();
            PrintSeperator();
            PrintExpr(e);
            PopIndent();
            PrintSeperator();
            TW.WriteLine(")");
        }

        public void PrintCheckSat()
        {
            TW.WriteLine("(check-sat)");
            TW.Flush();
        }

        public void PrintExit()
        {
            TW.WriteLine("(exit)");
            TW.Flush();
        }

        public void PrintSetOption(string option)
        {
            TW.WriteLine("(set-option :" + option + ")");
        }



        private void PushIndent()
        {
            if (HumanReadable)
            {
                var IDT = this.TW as IndentedTextWriter;
                IDT.Indent += this.Indent;
            }
        }

        private void PrintSeperator()
        {
            if (HumanReadable)
                TW.WriteLine("");
            else
                TW.Write(" ");
        }

        private void PopIndent()
        {
            if (HumanReadable)
            {
                var IDT = this.TW as IndentedTextWriter;
                IDT.Indent -= this.Indent;
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

        public Expr VisitIdentifierExpr(IdentifierExpr e)
        {
            // Should we make this check better by recording what variables are currently bound?
            if (!( ( e.Decl is SymbolicVariable ) || (e.Decl is BoundVariable )))
                throw new InvalidDataException("non symbolic/BoundVariable found in Expr"); //FIXME: Add our own Expr types

            TW.Write(e.Name);
            return e;
        }

        public Expr VisitOldExpr(OldExpr e)
        {
            throw new NotImplementedException ();
        }

        public Expr VisitCodeExpr(CodeExpr e)
        {
            throw new NotImplementedException ();
        }

        public Expr VisitBvExtractExpr(BvExtractExpr e)
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
            PushIndent();
            PrintSeperator();
            PrintExpr(e.Bitvector);
            PopIndent();
            PrintSeperator();
            TW.Write(")");
            return e;
        }

        public Expr VisitBvConcatExpr(BvConcatExpr e)
        {
            TW.Write("(concat");
            PushIndent();
            PrintSeperator();
            PrintExpr(e.E0);
            PrintSeperator();
            PrintExpr(e.E1);
            PopIndent();
            PrintSeperator();
            TW.Write(")");
            return e;
        }

        public Expr VisitForallExpr(ForallExpr e)
        {
            return PrintQuantifierExpr(e);
        }

        public Expr VisitExistExpr(ExistsExpr e)
        {
            return PrintQuantifierExpr(e);
        }

        private Expr PrintQuantifierExpr(QuantifierExpr QE)
        {
            if (QE is ExistsExpr)
                TW.Write("(exists");
            else if (QE is ForallExpr)
                TW.Write("(forall");
            else
                throw new NotSupportedException("Unsupported quantifier expr");

            PushIndent();
            PrintSeperator();
            TW.Write("(");
            PushIndent();
            PrintSeperator();

            foreach (var boundVar in QE.Dummies)
            {
                PrintSeperator();
                TW.Write("(" + boundVar.Name + " " + GetSMTLIBType(boundVar.TypedIdent.Type) + ")");
            }
            PopIndent();
            PrintSeperator();
            TW.Write(")");
            PrintSeperator();
            PrintExpr(QE.Body);
            PopIndent();
            PrintSeperator();
            TW.Write(")");
            return QE;
        }

        public Expr VisitLambdaExpr(LambdaExpr e)
        {
            throw new NotImplementedException ();
        }

        public Expr VisitNot(NAryExpr e)
        {
            return PrintUnaryOperator("not", e);
        }

        public Expr VisitNeg(NAryExpr e)
        {
            return PrintUnaryOperator("-", e);
        }

        public Expr VisitAdd(NAryExpr e)
        {
            return PrintBinaryOperator("+", e);
        }

        public Expr VisitSub(NAryExpr e)
        {
            return PrintBinaryOperator("-", e);
        }

        public Expr VisitMul(NAryExpr e)
        {
            return PrintBinaryOperator("*", e);
        }

        public Expr VisitDiv(NAryExpr e)
        {
            Debug.Assert(( e.Args[0] as Expr ).Type.IsInt && ( e.Args[1] as Expr ).Type.IsInt, "wrong types given to div!");
            return PrintBinaryOperator("div", e);
        }

        public Expr VisitMod(NAryExpr e)
        {
            return PrintBinaryOperator("mod", e);
        }

        public Expr VisitRealDiv(NAryExpr e)
        {
            Debug.Assert(( e.Args[0] as Expr ).Type.IsReal && ( e.Args[1] as Expr ).Type.IsReal, "wrong types given to div!");
            return PrintBinaryOperator("/", e);
        }

        public Expr VisitEq(NAryExpr e)
        {
            return PrintBinaryOperator("=", e);
        }

        public Expr VisitNeq(NAryExpr e)
        {
            // There isn't a != operator in SMTLIBv2 so construct the equivalent

            // We can't use Expr.Not here because it rewrites  Expr.Not(Expr.Eq(e.Args[0], e.Args[1]))
            // into the same expr as "e" which will cause infinite recursion.
            Expr temp = Expr.Unary(Token.NoToken, UnaryOperator.Opcode.Not, Expr.Eq(e.Args[0], e.Args[1]));
            PrintExpr(temp);
            return e;
        }

        public Expr VisitGt(NAryExpr e)
        {
            return PrintBinaryOperator(">", e);
        }

        public Expr VisitGe(NAryExpr e)
        {
            return PrintBinaryOperator(">=", e);
        }

        public Expr VisitLt(NAryExpr e)
        {
            return PrintBinaryOperator("<", e);
        }

        public Expr VisitLe(NAryExpr e)
        {
            return PrintBinaryOperator("<=", e);
        }

        public Expr VisitAnd (NAryExpr e)
        {
            return PrintBinaryOperator("and", e);
        }

        public Expr VisitOr(NAryExpr e)
        {
            return PrintBinaryOperator("or", e);
        }

        public Expr VisitImp(NAryExpr e)
        {
            return PrintBinaryOperator("=>", e);
        }

        public Expr VisitIff(NAryExpr e)
        {
            // There is not <==> operator in SMTLIBv2 so construct its equivalent
            Expr temp = Expr.And(Expr.Imp(e.Args[0], e.Args[1]), Expr.Imp(e.Args[1], e.Args[0]));
            PrintExpr(temp);
            return e;
        }

        public Expr VisitSubType(NAryExpr e)
        {
            throw new NotImplementedException ();
        }

        public Expr VisitMapStore(NAryExpr e)
        {
            // FIXME: Can we assert that we match the SMT-LIB order of args?
            return PrintTernaryOperator("store", e);
        }

        public Expr VisitMapSelect(NAryExpr e)
        {
            return PrintBinaryOperator("select", e);
        }

        public Expr VisitIfThenElse(NAryExpr e)
        {
            return PrintTernaryOperator("ite", e);
        }

        public Expr VisitFunctionCall(NAryExpr e)
        {
            var FC = e.Fun as FunctionCall;
            TW.Write("(" + FC.Func.Name);
            PushIndent();
            PrintSeperator();
            foreach (var param in e.Args)
            {
                PrintExpr(param);
                PrintSeperator(); // FIXME: There shouldn't be one on the last param
            }
            PopIndent();
            PrintSeperator();
            TW.Write(")");
            return e;
        }

        public Expr VisitTypeCoercion(NAryExpr e)
        {
            throw new NotImplementedException ();
        }

        public Expr VisitArithmeticCoercion(NAryExpr e)
        {
            throw new NotImplementedException ();
        }

        public Expr Visit_bvadd(NAryExpr e)
        {
            return PrintBinaryOperator("bvadd", e);
        }

        public Expr Visit_bvsub(NAryExpr e)
        {
            return PrintBinaryOperator("bvsub", e);
        }

        public Expr Visit_bvmul(NAryExpr e)
        {
            return PrintBinaryOperator("bvmul", e);
        }

        public Expr Visit_bvudiv(NAryExpr e)
        {
            return PrintBinaryOperator("bvudiv", e);
        }

        public Expr Visit_bvurem(NAryExpr e)
        {
            return PrintBinaryOperator("bvrem", e);
        }

        public Expr Visit_bvsdiv(NAryExpr e)
        {
            return PrintBinaryOperator("bvsdiv", e);
        }

        public Expr Visit_bvsrem(NAryExpr e)
        {
            return PrintBinaryOperator("bvsrem", e);
        }

        public Expr Visit_bvsmod(NAryExpr e)
        {
            return PrintBinaryOperator("bvsmod", e);
        }

        public Expr Visit_sign_extend(NAryExpr e)
        {
            return PrintSignExtend(e, "sign_extend");
        }

        public Expr Visit_zero_extend(NAryExpr e)
        {
            //  ((_ zero_extend i) (_ BitVec m) (_ BitVec m+i))
            // ((_ zero_extend i) x) means extend x with zeroes to the (unsigned)
            // equivalent bitvector of size m+i
            return PrintSignExtend(e, "zero_extend");
        }

        private Expr PrintSignExtend(NAryExpr e, string extensionType)
        {
            Debug.Assert(extensionType == "zero_extend" || extensionType == "sign_extend");
            Debug.Assert(e.Args.Count == 1);
            Debug.Assert(e.Args[0].Type.IsBv, "Not a bitvector!");
            Debug.Assert(e.Type.IsBv, "Out is not a bitvector!");

            // Work out extension amount
            int numberOfBitsToAdd = ( e.Type.BvBits - e.Args[0].Type.BvBits );
            Debug.Assert(numberOfBitsToAdd >= 0, "Number of bits to add calculation is incorrect"); // FIXME: Throw exception instead
            return PrintUnaryOperator("(_ " + extensionType + " " + numberOfBitsToAdd + ")", e);
        }

        public Expr Visit_bvneg(NAryExpr e)
        {
            return PrintBinaryOperator("bvneg", e);
        }

        public Expr Visit_bvand(NAryExpr e)
        {
            return PrintBinaryOperator("bvand", e);
        }

        public Expr Visit_bvor(NAryExpr e)
        {
            return PrintBinaryOperator("bvor", e);
        }

        public Expr Visit_bvnot(NAryExpr e)
        {
            return PrintUnaryOperator("bvnot", e);
        }

        public Expr Visit_bvxor(NAryExpr e)
        {
            return PrintBinaryOperator("bvxor", e);
        }

        public Expr Visit_bvshl (NAryExpr e)
        {
            return PrintBinaryOperator("bvshl", e);
        }

        public Expr Visit_bvlshr(NAryExpr e)
        {
            return PrintBinaryOperator("bvlshr", e);
        }

        public Expr Visit_bvashr(NAryExpr e)
        {
            return PrintBinaryOperator("bvashr", e);
        }

        public Expr Visit_bvult(NAryExpr e)
        {
            return PrintBinaryOperator("bvult", e);
        }

        public Expr Visit_bvule(NAryExpr e)
        {
            return PrintBinaryOperator("bvule", e);
        }

        public Expr Visit_bvugt(NAryExpr e)
        {
            return PrintBinaryOperator("bvugt", e);
        }

        public Expr Visit_bvuge(NAryExpr e)
        {
            return PrintBinaryOperator("bvuge", e);
        }

        public Expr Visit_bvslt(NAryExpr e)
        {
            return PrintBinaryOperator("bvslt", e);
        }

        public Expr Visit_bvsle(NAryExpr e)
        {
            return PrintBinaryOperator("bvsle", e);
        }

        public Expr Visit_bvsgt (NAryExpr e)
        {
            return PrintBinaryOperator("bvsgt", e);
        }

        public Expr Visit_bvsge(NAryExpr e)
        {
            return PrintBinaryOperator("bvsge", e);
        }

        // We go to a lot of effort in the Traverser to read the
        // string bvbuiltin to call the right method in IExprVisitor
        // but then we delegate back a single function for printing
        // binary operators using only the string name.
        // A bit inefficient...
        private Expr PrintBinaryOperator(string name, NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 2, "Incorrect number of arguments");
            TW.Write("(" + name);
            PushIndent();
            PrintSeperator();
            PrintExpr(e.Args[0]);
            PrintSeperator();
            PrintExpr(e.Args[1]);
            PopIndent();
            PrintSeperator();
            TW.Write(")");
            return e;
        }

        private Expr PrintUnaryOperator(string name, NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 1, "Incorrect number of arguments");
            TW.Write("(" + name);
            PushIndent();
            PrintSeperator();
            PrintExpr(e.Args[0]);
            PopIndent();
            PrintSeperator();
            TW.Write(")");
            return e;
        }

        private Expr PrintTernaryOperator(string name, NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 3, "Incorrect number of arguments");
            TW.Write("(" + name);
            PushIndent();
            PrintSeperator();
            PrintExpr(e.Args[0]);
            PrintSeperator();
            PrintExpr(e.Args[1]);
            PrintSeperator();
            PrintExpr(e.Args[2]);
            PopIndent();
            PrintSeperator();
            TW.Write(")");
            return e;
        }



    }
}

