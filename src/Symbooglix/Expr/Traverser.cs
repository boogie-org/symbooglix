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
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{
    public abstract class Traverser
    {
        protected IExprVisitor Visitor;

        public Traverser(IExprVisitor Visitor)
        {
            this.Visitor = Visitor;
        }

        public abstract Expr Traverse(Expr root);

        protected Expr Visit(Expr e)
        {
            // Handle Expressions that are of different types
            if (e is NAryExpr)
                return HandleNAry(e as NAryExpr);
            else if (e is LiteralExpr)
                return Visitor.VisitLiteralExpr(e as LiteralExpr);
            else if (e is IdentifierExpr)
                return Visitor.VisitIdentifierExpr(e as IdentifierExpr);
            else if (e is OldExpr)
                return Visitor.VisitOldExpr(e as OldExpr);
            else if (e is CodeExpr)
                return Visitor.VisitCodeExpr(e as CodeExpr);
            else if (e is BvExtractExpr)
                return Visitor.VisitBvExtractExpr(e as BvExtractExpr);
            else if (e is BvConcatExpr)
                return Visitor.VisitBvConcatExpr(e as BvConcatExpr);
            else if (e is ForallExpr)
                return Visitor.VisitForallExpr(e as ForallExpr);
            else if (e is ExistsExpr)
                return Visitor.VisitExistExpr(e as ExistsExpr);
            else if (e is LambdaExpr)
                return Visitor.VisitLambdaExpr(e as LambdaExpr);

            throw new NotImplementedException("Expr not supported!");
        }

        protected Expr HandleNAry(NAryExpr e)
        {
            if (e.Fun is FunctionCall)
            {
                var FC = (FunctionCall) e.Fun;
                string bvbuiltin = QKeyValue.FindStringAttribute(FC.Func.Attributes, "bvbuiltin");
                if (bvbuiltin != null)
                {
                    return HandlerBvBuiltIns(e, bvbuiltin);
                }
                else
                {
                    string builtin = QKeyValue.FindStringAttribute(FC.Func.Attributes, "builtin");
                    if (builtin != null)
                        return HandlerBuiltIns(e, builtin);

                    // Not a bvbuiltin so treat as generic function call.
                    return Visitor.VisitFunctionCall(e);
                }

            }
            else if (e.Fun is UnaryOperator)
            {
                var U = (UnaryOperator) e.Fun;
                switch (U.Op)
                {
                    case UnaryOperator.Opcode.Neg:
                        return Visitor.VisitNeg(e);
                    case UnaryOperator.Opcode.Not:
                        return Visitor.VisitNot(e);
                    default:
                        throw new NotImplementedException("Unary operator not supported");
                }
            }
            else if (e.Fun is BinaryOperator)
            {
                var B = (BinaryOperator) e.Fun;
                switch (B.Op)
                {
                    // Integer or Real number operators
                    case BinaryOperator.Opcode.Add:
                        return Visitor.VisitAdd(e);
                    case BinaryOperator.Opcode.Sub:
                        return Visitor.VisitSub(e);
                    case BinaryOperator.Opcode.Mul:
                        return Visitor.VisitMul(e);
                    case BinaryOperator.Opcode.Div:
                        return Visitor.VisitDiv(e);
                    case BinaryOperator.Opcode.Mod:
                        return Visitor.VisitMod(e);
                    case BinaryOperator.Opcode.RealDiv:
                        return Visitor.VisitRealDiv(e);
                    case BinaryOperator.Opcode.Pow:
                        return Visitor.VisitPow(e);
                    
                    // Comparision operators
                    case BinaryOperator.Opcode.Eq:
                        return Visitor.VisitEq(e);
                    case BinaryOperator.Opcode.Neq:
                        return Visitor.VisitNeq(e);
                    case BinaryOperator.Opcode.Gt:
                        return Visitor.VisitGt(e);
                    case BinaryOperator.Opcode.Ge:
                        return Visitor.VisitGe(e);
                    case BinaryOperator.Opcode.Lt:
                        return Visitor.VisitLt(e);
                    case BinaryOperator.Opcode.Le:
                        return Visitor.VisitLe(e);

                    // Bool operators
                    case BinaryOperator.Opcode.And:
                        return Visitor.VisitAnd(e);
                    case BinaryOperator.Opcode.Or:
                        return Visitor.VisitOr(e);
                    case BinaryOperator.Opcode.Imp:
                        return Visitor.VisitImp(e);
                    case BinaryOperator.Opcode.Iff:
                        return Visitor.VisitIff(e);
                    case BinaryOperator.Opcode.Subtype:
                        return Visitor.VisitSubType(e);
                    
                    default:
                        throw new NotImplementedException("Binary operator not supported!");

                }
            }
            else if (e.Fun is MapStore)
            {
                return Visitor.VisitMapStore(e);
            }
            else if (e.Fun is MapSelect)
            {
                return Visitor.VisitMapSelect(e);
            }
            else if (e.Fun is IfThenElse)
            {
                return Visitor.VisitIfThenElse(e);
            }
            else if (e.Fun is TypeCoercion)
            {
                return Visitor.VisitTypeCoercion(e);
            }
            else if (e.Fun is ArithmeticCoercion)
            {
                return Visitor.VisitArithmeticCoercion(e);
            }
            else if (e.Fun is DistinctOperator)
            {
                return Visitor.VisitDistinct(e);
            }

            throw new NotImplementedException("NAry not handled!");
        }

        protected Expr HandlerBuiltIns(NAryExpr e, string builtin)
        {
            // We support very few builtins here. People shouldn't be using them
            switch (builtin)
            {
                case "div":
                    return Visitor.VisitDiv(e);
                case "mod":
                    return Visitor.VisitMod(e);
                case "rem":
                    return Visitor.VisitRem(e);
                default:
                    throw new NotImplementedException("Builtin \"" + builtin + "\" not supported");
            }
        }

        protected Expr HandlerBvBuiltIns(NAryExpr e, string builtin)
        {
            Debug.Assert(builtin.Length > 0);

            // We grab for first word because the bvbuiltin
            // might be "zeroextend 16", we don't care about the number
            string firstWord = builtin.Split(' ')[0];
            Debug.Assert(firstWord.Length > 0);
            switch (firstWord)
            {
                // arithmetic
                case "bvadd":
                    return Visitor.Visit_bvadd(e);
                case "bvsub":
                    return Visitor.Visit_bvsub(e);
                case "bvmul":
                    return Visitor.Visit_bvmul(e);
                case "bvudiv":
                    return Visitor.Visit_bvudiv(e);
                case "bvurem":
                    return Visitor.Visit_bvurem(e);
                case "bvsdiv":
                    return Visitor.Visit_bvsdiv(e);
                case "bvsrem":
                    return Visitor.Visit_bvsrem(e);
                case "bvsmod":
                    return Visitor.Visit_bvsmod(e);
                case "sign_extend":
                    return Visitor.Visit_sign_extend(e);
                case "zero_extend":
                    return Visitor.Visit_zero_extend(e);
                
                // bitwise logical
                case "bvneg":
                    return Visitor.Visit_bvneg(e);
                case "bvand":
                    return Visitor.Visit_bvand(e);
                case "bvor":
                    return Visitor.Visit_bvor(e);
                case "bvnot":
                    return Visitor.Visit_bvnot(e);
                case "bvxor":
                    return Visitor.Visit_bvxor(e);

                // shift
                case "bvshl":
                    return Visitor.Visit_bvshl(e);
                case "bvlshr":
                    return Visitor.Visit_bvlshr(e);
                case "bvashr":
                    return Visitor.Visit_bvashr(e);

                // Comparison
                case "bvult":
                    return Visitor.Visit_bvult(e);
                case "bvule":
                    return Visitor.Visit_bvule(e);
                case "bvugt":
                    return Visitor.Visit_bvugt(e);
                case "bvuge":
                    return Visitor.Visit_bvuge(e);
                case "bvslt":
                    return Visitor.Visit_bvslt(e);
                case "bvsle":
                    return Visitor.Visit_bvsle(e);
                case "bvsgt":
                    return Visitor.Visit_bvsgt(e);
                case "bvsge":
                    return Visitor.Visit_bvsge(e);
                default:
                    throw new NotImplementedException(firstWord + " bvbuiltin not supported!");
            }
        }
    }
}

