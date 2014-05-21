using System;
using Microsoft.Boogie;
using Action = symbooglix.Traverser.Action;

namespace symbooglix
{
    public interface IExprVisitor
    {
        // Visiting is simple using double dispatch
        Action VisitLiteralExpr(LiteralExpr e);
        Action VisitIdentifierExpr(IdentifierExpr e);
        Action VisitOldExpr(OldExpr e);
        Action VisitCodeExpr(CodeExpr e);
        Action VisitBvExtractExpr(BvExtractExpr e);
        Action VisitBvConcatExpr(BvConcatExpr e);
        Action VisitForallExpr(ForallExpr e);
        Action VisitExistExpr(ExistsExpr e);
        Action VisitLambdaExpr(LambdaExpr e);

        // All these are NAryExpr, double dispatch won't work here!

        // Unary built-ins
        Action VisitNot(NAryExpr e);
        Action VisitNeg(NAryExpr e);

        // Binary built-ins

        // Real number operators
        Action VisitAdd(NAryExpr e);
        Action VisitSub(NAryExpr e);
        Action VisitMul(NAryExpr e);
        Action VisitDiv(NAryExpr e); // Is this flooring division?
        Action VisitMod(NAryExpr e);
        Action VisitRealDiv(NAryExpr e);

        // Comparision operators for all types
        Action VisitEq(NAryExpr e);
        Action VisitNeq(NAryExpr e);
        Action VisitGt(NAryExpr e);
        Action VisitGe(NAryExpr e);
        Action VisitLt(NAryExpr e);
        Action VisitLe(NAryExpr e);

        // Bool operators
        Action VisitAnd(NAryExpr e);
        Action VisitOr(NAryExpr e);
        Action VisitImp(NAryExpr e);
        Action VisitIff(NAryExpr e);

        // What does this do?
        Action VisitSubType(NAryExpr e);

        // Map operations
        Action VisitMapStore(NAryExpr e);
        Action VisitMapSelect(NAryExpr e);

        Action VisitIfThenElse(NAryExpr e);

        // Only visited if not SMT-LIBv2 bitvector function
        Action VisitFunctionCall(NAryExpr e);

        // Do we even need these?
        Action VisitTypeCoercion(NAryExpr e);
        Action VisitArithmeticCoercion(NAryExpr e);

        // SMT-LIB bitvector functions except
        // bitvector extraction and concat...
        // for some reason these are their own
        // Expr class. Urghh inconsistent design :(

        // Arithmetic
        Action Visit_bvadd(NAryExpr e);
        Action Visit_bvsub(NAryExpr e);
        Action Visit_bvmul(NAryExpr e);
        Action Visit_bvudiv(NAryExpr e);
        Action Visit_bvurem(NAryExpr e);
        Action Visit_bvsdiv(NAryExpr e);
        Action Visit_bvsrem(NAryExpr e);
        Action Visit_bvsmod(NAryExpr e);
        Action Visit_sign_extend(NAryExpr e);
        Action Visit_zero_extend(NAryExpr e);

        // Bitwise operators
        // Do we need to support some of the more exotic things like bvnand?
        Action Visit_bvneg(NAryExpr e);
        Action Visit_bvand(NAryExpr e);
        Action Visit_bvor(NAryExpr e);
        Action Visit_bvnot(NAryExpr e);
        Action Visit_bvxor(NAryExpr e);

        // Shifts
        Action Visit_bvshl(NAryExpr e);
        Action Visit_bvlshr(NAryExpr e);
        Action Visit_bvashr(NAryExpr e);

        // unsigned comparision
        Action Visit_bvult(NAryExpr e);
        Action Visit_bvule(NAryExpr e);
        Action Visit_bvugt(NAryExpr e);
        Action Visit_bvuge(NAryExpr e);

        // signed comparision
        Action Visit_bvslt(NAryExpr e);
        Action Visit_bvsle(NAryExpr e);
        Action Visit_bvsgt(NAryExpr e);
        Action Visit_bvsge(NAryExpr e);

    }
}

