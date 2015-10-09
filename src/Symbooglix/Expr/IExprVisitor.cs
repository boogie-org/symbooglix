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

namespace Symbooglix
{
    public interface IExprVisitor
    {
        // Visiting is simple using double dispatch
        Expr VisitLiteralExpr(LiteralExpr e);
        Expr VisitIdentifierExpr(IdentifierExpr e);
        Expr VisitOldExpr(OldExpr e);
        Expr VisitCodeExpr(CodeExpr e);
        Expr VisitBvExtractExpr(BvExtractExpr e);
        Expr VisitBvConcatExpr(BvConcatExpr e);
        Expr VisitForallExpr(ForallExpr e);
        Expr VisitExistExpr(ExistsExpr e);
        Expr VisitLambdaExpr(LambdaExpr e);

        // All these are NAryExpr, double dispatch won't work here!

        // Unary built-ins
        Expr VisitNot(NAryExpr e);
        Expr VisitNeg(NAryExpr e);

        // Binary built-ins

        // Real number operators
        Expr VisitAdd(NAryExpr e);
        Expr VisitSub(NAryExpr e);
        Expr VisitMul(NAryExpr e);
        Expr VisitDiv(NAryExpr e); // Is this flooring division?
        Expr VisitMod(NAryExpr e);
        Expr VisitRem(NAryExpr e); // This is a Z3 extension
        Expr VisitRealDiv(NAryExpr e);
        Expr VisitPow(NAryExpr e);

        // Comparision operators for all types
        Expr VisitEq(NAryExpr e);
        Expr VisitNeq(NAryExpr e);
        Expr VisitGt(NAryExpr e);
        Expr VisitGe(NAryExpr e);
        Expr VisitLt(NAryExpr e);
        Expr VisitLe(NAryExpr e);

        // Bool operators
        Expr VisitAnd(NAryExpr e);
        Expr VisitOr(NAryExpr e);
        Expr VisitImp(NAryExpr e);
        Expr VisitIff(NAryExpr e);

        // What does this do?
        Expr VisitSubType(NAryExpr e);

        // Map operations
        Expr VisitMapStore(NAryExpr e);
        Expr VisitMapSelect(NAryExpr e);

        Expr VisitIfThenElse(NAryExpr e);

        // Only visited if not SMT-LIBv2 bitvector function
        Expr VisitFunctionCall(NAryExpr e);

        // Do we even need these?
        Expr VisitTypeCoercion(NAryExpr e);
        Expr VisitArithmeticCoercion(NAryExpr e);

        // SMT-LIB bitvector functions except
        // bitvector extraction and concat...
        // for some reason these are their own
        // Expr class. Urghh inconsistent design :(

        // Arithmetic
        Expr Visit_bvadd(NAryExpr e);
        Expr Visit_bvsub(NAryExpr e);
        Expr Visit_bvmul(NAryExpr e);
        Expr Visit_bvudiv(NAryExpr e);
        Expr Visit_bvurem(NAryExpr e);
        Expr Visit_bvsdiv(NAryExpr e);
        Expr Visit_bvsrem(NAryExpr e);
        Expr Visit_bvsmod(NAryExpr e);
        Expr Visit_sign_extend(NAryExpr e);
        Expr Visit_zero_extend(NAryExpr e);

        // Bitwise operators
        // Do we need to support some of the more exotic things like bvnand?
        Expr Visit_bvneg(NAryExpr e);
        Expr Visit_bvand(NAryExpr e);
        Expr Visit_bvor(NAryExpr e);
        Expr Visit_bvnot(NAryExpr e);
        Expr Visit_bvxor(NAryExpr e);

        // Shifts
        Expr Visit_bvshl(NAryExpr e);
        Expr Visit_bvlshr(NAryExpr e);
        Expr Visit_bvashr(NAryExpr e);

        // unsigned comparision
        Expr Visit_bvult(NAryExpr e);
        Expr Visit_bvule(NAryExpr e);
        Expr Visit_bvugt(NAryExpr e);
        Expr Visit_bvuge(NAryExpr e);

        // signed comparision
        Expr Visit_bvslt(NAryExpr e);
        Expr Visit_bvsle(NAryExpr e);
        Expr Visit_bvsgt(NAryExpr e);
        Expr Visit_bvsge(NAryExpr e);

        Expr VisitDistinct(NAryExpr e);

    }
}

