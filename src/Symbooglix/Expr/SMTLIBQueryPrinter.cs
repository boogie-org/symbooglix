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
        private HashSet<Microsoft.Boogie.TypeCtorDecl> sortsToDeclare = null;
        private FindSymbolicsVisitor FSV = null;
        private FindUinterpretedFunctionsVisitor FFV = null;
        private TextWriter TW = null;
        private Traverser TheTraverser = null;
        public bool HumanReadable;
        private int Indent;

        // Tweaks to annotations
        public bool AnnotateVariableUses = true;
        public bool AnnotateAssertsWithNames = true;

        private int AssertCounter = 0;

        // Used for :named attributed expressions
        private static readonly string BindingPrefix = "N";
        private int NamedAttributeCounter = 0;
        private Dictionary<Expr, int> Bindings;
        private bool UseNamedAttributeBindings;
        private bool NamedBindingsDisabledInQuantifierExpr;
        private ExprCountingVisitor BindingsFinder;

        private bool PrintTriggers;

        public SMTLIBQueryPrinter(TextWriter TW, bool useNamedAttributeBindings, bool humanReadable, bool printTriggers = true, int indent=2)
        {
            this.HumanReadable = humanReadable; // Must be set before output is set
            ChangeOutput(TW);
            this.Indent = indent;

            // FIXME: These declarations are broken. Declarations are part of the push-and-pop stack but we
            // are treating them globally here. This is a mess.
            symbolicsToDeclare = new HashSet<SymbolicVariable>();
            functionsToDeclare = new HashSet<Function>();
            sortsToDeclare = new HashSet<TypeCtorDecl>();
            FSV = new FindSymbolicsVisitor(symbolicsToDeclare); // Have the visitor use our container
            FFV = new FindUinterpretedFunctionsVisitor(functionsToDeclare); // Have the visitor use our container
            BindingsFinder = new ExprCountingVisitor();

            // FIXME: This is a hack. Boogie's GetHashCode() is very expensive
            // so we just check for reference equality instead
            Bindings = new Dictionary<Expr, int>( new ExprReferenceCompare());
            this.UseNamedAttributeBindings = useNamedAttributeBindings;
            this.NamedBindingsDisabledInQuantifierExpr = false;
            PrintTriggers = printTriggers;

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
            // We never want to use bindings for these
            if (!UseNamedAttributeBindings || NamedBindingsDisabledInQuantifierExpr || root is LiteralExpr || root is IdentifierExpr)
            {
                TheTraverser.Traverse(root);
                return;
            }

            int numberOfOccurances = BindingsFinder.ExpressionCount[root];
            if (numberOfOccurances < 2)
            {
                TheTraverser.Traverse(root);
                return;
            }

            Debug.Assert(numberOfOccurances >= 2);
            try
            {
                // Use the Binding assigned to this Expr if it's available.
                int BindingNumber = Bindings[root];
                TW.Write(BindingPrefix + Bindings[root].ToString());
                return;
            }
            catch (KeyNotFoundException)
            {
                // The binding hasn't been made yet so print it
                // Print the Expr and give it a binding
                int bindingNumber = NamedAttributeCounter;
                var binding = BindingPrefix + bindingNumber.ToString();
                ++NamedAttributeCounter; // Increment for next user.

                TW.Write("(!");
                PrintSeperator();
                PushIndent();

                // Inside a Quantified Expr :named attributes are not allowed
                // to contain free variables. We may miss opportunities here to
                // add bindings but it is safer to just completly disable adding bindings
                // inside a Quantified Expr
                if (root is QuantifierExpr)
                    NamedBindingsDisabledInQuantifierExpr = true;

                TheTraverser.Traverse(root);

                // Now we are outside a quantifier bindings can be allowed again
                if (root is QuantifierExpr)
                    NamedBindingsDisabledInQuantifierExpr = false;

                PrintSeperator();
                TW.Write(":named " + binding);
                PopIndent();
                PrintSeperator();
                TW.Write(")");

                // Save the binding
                Bindings[root] = bindingNumber;
            }
        }

        public void ClearDeclarations()
        {
            symbolicsToDeclare.Clear();
            functionsToDeclare.Clear();
            sortsToDeclare.Clear();

            if (UseNamedAttributeBindings)
            {
                // FIXME: These don't really belong here
                BindingsFinder.Clear();
                Bindings.Clear();
                NamedAttributeCounter = 0;
            }
        }

        // For this verion of AddDeclarations we already know what variables
        // and uninterpreted functions are used.
        public void AddDeclarations(Constraint c)
        {
            // Add variables used in Constraint
            foreach (var usedVariable in c.UsedVariables)
            {
                symbolicsToDeclare.Add(usedVariable);
            }

            // Add uninterpreted functions used in Constraint
            foreach (var usedUninterpretedFunction in c.UsedUninterpretedFunctions)
            {
                functionsToDeclare.Add(usedUninterpretedFunction);
            }

            if (UseNamedAttributeBindings)
                BindingsFinder.Visit(c.Condition);
        }

        public void AddDeclarations(Expr e)
        {
            FSV.Visit(e); // We don't know what variables are used here so find them by traversing the Expr
            FFV.Visit(e); // We don't know what uninterpreted functions are sued here so find them by traversing Expr

            if (UseNamedAttributeBindings)
                BindingsFinder.Visit(e);
        }


        public enum Logic
        {
            DO_NOT_SET, /* Special Value that won't be printed */
            QF_BV,
            QF_ABV,
            QF_AUFBV, // Quantifier free, arrays, uninterpreted functions and bitvectors
            ALL_SUPPORTED // CVC4 specific
        }

        public void ChangeOutput(TextWriter newTW)
        {
            Debug.Assert(newTW != null, "New output cannot be null!");
            if (HumanReadable)
            {
                this.TW = new IndentedTextWriter(newTW," ");
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

        private void AddSort(Microsoft.Boogie.Type typ)
        {
            if (typ.IsCtor) {
                var typAsCtor = typ.AsCtor;
                if (typAsCtor.Arguments.Count > 0)
                    throw new NotSupportedException("Can't handle constructor types with arguments");

                sortsToDeclare.Add(typ.AsCtor.Decl);
            } else if (typ.IsMap) {
                // Maps might use constructor types
                var typAsMap = typ.AsMap;
                foreach (var arg in typAsMap.Arguments) {
                    AddSort(arg);
                }
                AddSort(typAsMap.Result);
            }
        }

        private static string GetCustomSortName(Microsoft.Boogie.TypeCtorDecl typeDecl)
        {
            // FIXME: Do proper mangling to avoid name clashes
            return "@" + typeDecl.Name;
        }

        public void PrintSortDeclarations()
        {
            if (HumanReadable)
                PrintCommentLine("Start custom sort declarations");

            // Compute sorts used (we assume all AddDeclaration(...) calls have been made)
            foreach (var v in symbolicsToDeclare)
            {
                AddSort(v.TypedIdent.Type);
            }

            foreach (var f in functionsToDeclare)
            {
                foreach (var arg in f.InParams.Concat(f.OutParams))
                {
                    AddSort(arg.TypedIdent.Type);
                }
            }

            // FIXME: We probably need to check free variables too!

            foreach (var sort in sortsToDeclare)
            {
                TW.WriteLine("(declare-sort " + GetCustomSortName(sort) + ")");
            }

            if (HumanReadable)
                PrintCommentLine("End custom sort declarations");
        }

        public void PrintFunctionDeclarations()
        {
            if (HumanReadable)
                PrintCommentLine("Start function declarations");

            foreach (var function in functionsToDeclare)
            {
                if (function.Body != null)
                    throw new NotSupportedException("Hit function that should of been inlined!");

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
            Microsoft.Boogie.Type theType = null;

            // Handle type synonyms. E.g. ``type arrayId = bv2``
            // Perhaps we should run a pass in the program to remove
            // type synonyms?
            theType = T;
            while (theType is TypeSynonymAnnotation)
            {
                theType = ( theType as TypeSynonymAnnotation ).ExpandedType;
            }

            if (theType is BvType)
            {
                var BVT = theType as BvType;
                return "(_ BitVec " + BVT.Bits + ")";
            }
            else if (theType is BasicType)
            {
                var ST = ( theType as BasicType ).T;
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
            else if (theType is MapType)
            {
                var MT = theType as MapType;
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
            else if (theType is CtorType)
            {
                var CT = theType as CtorType;
                return GetCustomSortName(CT.Decl);
            }
            else
            {
                throw new NotImplementedException("The type " + theType.ToString() + " is not supported");
            }
        }

        public void PrintSetLogic(Logic L)
        {
            if ( L != Logic.DO_NOT_SET)
                TW.WriteLine("(set-logic " + L.ToString() + " )");
        }

        public void PrintPushDeclStack(int count)
        {
            if (count < 1)
                throw new ArgumentException("count must be > 0");

            // FIXME: We should be keeping our decls in a stack so we can push and pop them
            TW.WriteLine("(push {0})", count);
        }

        public void PrintPopDeclStack(int count)
        {
            if (count < 1)
                throw new ArgumentException("count must be > 0");

            // FIXME: We should be keeping our decls in a stack so we can push and pop them
            TW.WriteLine("(pop {0})", count);
        }

        public void PrintAssert(Expr e)
        {
            TW.Write("(assert");
            PushIndent();

            if (HumanReadable && AnnotateAssertsWithNames)
            {
                PrintSeperator();
                TW.Write("(!");
                PushIndent();

            }
            PrintSeperator();

            PrintExpr(e);
            PopIndent();


            if (HumanReadable && AnnotateAssertsWithNames)
            {
                PrintSeperator();
                TW.Write(":named assert" + AssertCounter.ToString());
                PrintSeperator();
                TW.Write(")");
                PopIndent();

            }
            PrintSeperator();

            TW.WriteLine(")");

            ++AssertCounter;
        }

        public void PrintCheckSat()
        {
            TW.WriteLine("(check-sat)");
            TW.Flush();
        }

        public void PrintGetModel()
        {
            TW.WriteLine("(get-model)");
            TW.Flush();
        }

        public void PrintGetUnsatCore()
        {
            TW.WriteLine("(get-unsat-core)");
            TW.Flush();
        }

        public void PrintExit()
        {
            TW.WriteLine("(exit)");
            Reset();
        }

        public void Reset()
        {
            TW.Flush();
            AssertCounter = 0;
            ClearDeclarations();
        }

        public void PrintReset()
        {
            TW.WriteLine("(reset)");
            Reset();
        }

        // FIXME: This API is gross. Use enums instead
        public void PrintSetOption(string option, string value)
        {
            TW.WriteLine("(set-option :" + option + " " + value + ")");
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
                // Int
                TW.Write(e.asBigNum);
            }
            else if (e.isBigDec)
            {
                // Real
                TW.Write(e.asBigDec.ToDecimalString());
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


            if (HumanReadable && AnnotateVariableUses && e.Decl is SymbolicVariable)
            {
                TW.Write(" ;" + ( e.Decl as SymbolicVariable ).Origin.ToString());
            }
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

            // Handle Triggers
            if (QE.Triggers == null || !PrintTriggers)
            {
                PrintExpr(QE.Body);
            }
            else
            {
                TW.Write("(!");
                PushIndent();
                PrintSeperator();

                PrintExpr(QE.Body);
                PrintSeperator();

                // fixme: pos!
                // Print triggers
                var trigger = QE.Triggers;
                if (trigger.Pos)
                {
                    while (trigger != null)
                    {
                        // list of expressions
                        TW.Write(":pattern (");
                        PushIndent();
                        PrintSeperator();
                        foreach (var triggerExpr in trigger.Tr)
                        {
                            PrintExpr(triggerExpr);
                            PrintSeperator();
                        }
                        PopIndent();
                        TW.Write(")");
                        trigger = trigger.Next;
                    }
                }
                else
                {
                    if (trigger.Tr.Count != 1)
                        throw new InvalidDataException("Negative trigger is malformed");

                    // no-pattern takes an expression rather than a list of expressions
                    TW.Write(":no-pattern");
                    PushIndent();
                    PrintSeperator();
                    PrintExpr(trigger.Tr[0]);
                    PopIndent();
                }

                PopIndent();
                PrintSeperator();
                TW.Write(")");
            }

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

        public Expr VisitRem(NAryExpr e)
        {
            // FIXME: This is a Z3 extension, we need to emit something different for other solvers
            Debug.Assert(( e.Args[0] as Expr ).Type.IsInt && ( e.Args[1] as Expr ).Type.IsInt, "wrong types given to rem");
            return PrintBinaryOperator("rem", e);
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

        public Expr VisitPow(NAryExpr e)
        {
            throw new NotImplementedException();
        }

        public Expr VisitEq(NAryExpr e)
        {
            return PrintBinaryOperator("=", e);
        }

        public Expr VisitNeq(NAryExpr e)
        {
            return PrintBinaryOperator("distinct", e);
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
            // There is not <==> operator in SMTLIBv2 so print its equivalent
            // We cannot construct the equivalent and then print that because that would
            // break the binding as we'd be introducing Expr that haven't been seen before.
            TW.Write("(and");
            PushIndent();

            PrintSeperator();
            TW.Write("(=>");
            PushIndent();
            PrintSeperator();
            PrintExpr(e.Args[0]);
            PrintSeperator();
            PrintExpr(e.Args[1]);
            PopIndent();
            PrintSeperator();
            TW.Write(")");

            PrintSeperator();
            TW.Write("(=>");
            PushIndent();
            PrintSeperator();
            PrintExpr(e.Args[1]);
            PrintSeperator();
            PrintExpr(e.Args[0]);
            PopIndent();
            PrintSeperator();
            TW.Write(")");

            PopIndent();
            PrintSeperator();
            TW.Write(")");
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

            if (e.Args.Count == 0)
            {
                // A function with argments does not need parentheses
                TW.WriteLine(FC.Func.Name);
                return e;
            }

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
            Debug.Assert(e.Args.Count == 1);
            var typeCoercion = e.Fun as TypeCoercion;
            if (!typeCoercion.Type.Equals(e.Args[0].Type))
                throw new NotSupportedException("Non trivial type coercion used");

            // Completly ignore the type coercion
            PrintExpr(e.Args[0]);
            return e;
        }

        public Expr VisitArithmeticCoercion(NAryExpr e)
        {
            Debug.Assert(e.Args.Count == 1);
            Debug.Assert(e.Fun is ArithmeticCoercion);

            var arithmeticCoercion = e.Fun as ArithmeticCoercion;
            switch (arithmeticCoercion.Coercion)
            {
                case ArithmeticCoercion.CoercionType.ToInt:
                    return PrintUnaryOperator("to_int", e);
                case ArithmeticCoercion.CoercionType.ToReal:
                    return PrintUnaryOperator("to_real", e);
                default:
                    throw new NotSupportedException("Arithmetic coercion type " + arithmeticCoercion.Coercion + " not supported");
            }
        }

        public Expr VisitDistinct(NAryExpr e)
        {
            TW.Write("(distinct");
            PushIndent();
            PrintSeperator();
            for (int index = 0; index < e.Args.Count; ++index)
            {
                PrintExpr(e.Args[index]);

                if (index < (e.Args.Count -1))
                    PrintSeperator();
            }
            PopIndent();
            PrintSeperator();
            TW.Write(")");;
            return e;
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
            return PrintBinaryOperator("bvurem", e);
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
            return PrintUnaryOperator("bvneg", e);
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

    // FIXME: This is not specific to the SMTLIBQueryPrinter and does not count all nodes.
    // This should be made internal to the printer.
    public class ExprCountingVisitor : ReadOnlyVisitor
    {
        public Dictionary<Expr, int> ExpressionCount;

        public void Clear()
        {
            ExpressionCount.Clear();
        }

        public ExprCountingVisitor()
        {
            // FIXME: This is a hack. Boogie's GetHashCode() is very expensive
            // so we just check for reference equality instead
            this.ExpressionCount = new Dictionary<Expr, int>(new ExprReferenceCompare());
        }

        public override Expr VisitExpr(Expr node)
        {
            // This avoids recording the same node twice
            // as VisitExpr() can call VisitNAryExpr() and VisitQuantifier()
            if (node is NAryExpr || node is QuantifierExpr)
                return base.VisitExpr(node);

            // We don't want to record anything for these
            if (node is LiteralExpr || node is IdentifierExpr)
                return base.VisitExpr(node);

            // We don't need to visit a nodes children if it
            // was already seen before because that means it will
            // get abbreviated in the printer. If we visit the children again we will over
            // count because when the abbreviation happens in the printer
            // the children won't be printed again.
            bool goDeeper = CountExpr(node);
            if (goDeeper)
                return base.VisitExpr(node);
            else
                return node;
        }

        // This is necessary because the root of a tree might
        // be an NAryExpr so the double dispatch won't call
        // VisitExpr() but instead will call VisitNAryExpr
        public override Expr VisitNAryExpr(NAryExpr node)
        {
            bool goDeeper = CountExpr(node);
            if (goDeeper)
                return base.VisitNAryExpr(node);
            else
                return node;
        }

        // This is necessary because the root of the Tree might be a QuantifierExpr
        public override QuantifierExpr VisitQuantifierExpr(QuantifierExpr node)
        {
            bool goDeeper = CountExpr(node);

            if (goDeeper)
                return base.VisitQuantifierExpr(node);
            else
                return node;
        }

        // Return true iff the node has not been seen before, otherwise false
        private bool CountExpr(Expr node)
        {
            try
            {
                int currentCount = ExpressionCount[node];

                ExpressionCount[node] = currentCount +1;
                return false;
            }
            catch (KeyNotFoundException )
            {
                ExpressionCount[node] = 1;
                return true;
            }
        }
    }
}

