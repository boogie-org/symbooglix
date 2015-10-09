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
    // This is a hack. Really this needs to go into upstream Boogie
    // as virtual methods. We manually dispatch by hand (eurgh...) to simulate virtual methods
    public static class BoogieExprExtensions
    {
        public static int GetNumberOfChildren(this Expr e)
        {
            if (e is LiteralExpr)
                return (e as LiteralExpr).GetNumberOfChildren ();
            else if (e is IdentifierExpr)
                return (e as IdentifierExpr).GetNumberOfChildren ();
            else if (e is NAryExpr)
                return (e as NAryExpr).GetNumberOfChildren ();
            else if (e is BvExtractExpr)
                return (e as BvExtractExpr).GetNumberOfChildren ();
            else if (e is BvConcatExpr)
                return (e as BvConcatExpr).GetNumberOfChildren ();
            else if (e is ForallExpr)
                return (e as ForallExpr).GetNumberOfChildren ();
            else if (e is ExistsExpr)
                return (e as ExistsExpr).GetNumberOfChildren ();
            else if (e is OldExpr)
                return (e as OldExpr).GetNumberOfChildren();
            else
                throw new NotImplementedException();
        }

        // FIXME: We should probably do some type checking here
        public static void SetChild(this Expr e, int number, Expr NewChild)
        {
            if (e is LiteralExpr)
                (e as LiteralExpr).SetChild(number, NewChild);
            else if (e is IdentifierExpr)
                (e as IdentifierExpr).SetChild(number, NewChild);
            else if (e is NAryExpr)
                (e as NAryExpr).SetChild(number, NewChild);
            else if (e is BvExtractExpr)
                (e as BvExtractExpr).SetChild(number, NewChild);
            else if (e is BvConcatExpr)
                (e as BvConcatExpr).SetChild(number, NewChild);
            else if (e is ForallExpr)
                (e as ForallExpr).SetChild(number, NewChild);
            else if (e is ExistsExpr)
                (e as ExistsExpr).SetChild(number, NewChild);
            else if (e is OldExpr)
                (e as OldExpr).SetChild(number, NewChild);
            else
                throw new NotImplementedException();
        }

        public static Expr GetChild(this Expr e, int number)
        {
            if (e is LiteralExpr)
                return (e as LiteralExpr).GetChild(number);
            else if (e is IdentifierExpr)
                return (e as IdentifierExpr).GetChild(number);
            else if (e is NAryExpr)
                return (e as NAryExpr).GetChild(number);
            else if (e is BvExtractExpr)
                return (e as BvExtractExpr).GetChild(number);
            else if (e is BvConcatExpr)
                return (e as BvConcatExpr).GetChild(number);
            else if (e is ForallExpr)
                return (e as ForallExpr).GetChild(number);
            else if (e is ExistsExpr)
                return (e as ExistsExpr).GetChild(number);
            else if (e is OldExpr)
                return (e as OldExpr).GetChild(number);
            else
                throw new NotImplementedException();
        }

        // LiteralExpr
        public static int GetNumberOfChildren(this LiteralExpr e)
        {
            return 0;
        }

        public static void SetChild(this LiteralExpr e, int number, Expr NewChild)
        {
            throw new InvalidOperationException("Cannot set child of a leaf node");
        }

        public static Expr GetChild(this LiteralExpr e, int number)
        {
            throw new InvalidOperationException("Cannot get child of a leaf node");
        }

        // IdentiferExpr
        public static int GetNumberOfChildren(this IdentifierExpr e)
        {
            return 0;
        }

        public static void SetChild(this IdentifierExpr e, int number, Expr NewChild)
        {
            throw new InvalidOperationException("Cannot set child of a leaf node");
        }

        public static Expr GetChild(this IdentifierExpr e, int number)
        {
            throw new InvalidOperationException("Cannot get child of a leaf node");
        }

        // NAryExpr
        public static int GetNumberOfChildren(this NAryExpr e)
        {
            return e.Args.Count;
        }

        public static void SetChild(this NAryExpr e, int number, Expr NewChild)
        {
            e.Args[number] = NewChild;
        }

        public static Expr GetChild(this NAryExpr e, int number)
        {
            return e.Args[number];
        }

        // BvExtractExpr
        public static int GetNumberOfChildren(this BvExtractExpr e)
        {
            return 1;
        }

        public static void SetChild(this BvExtractExpr e, int number, Expr NewChild)
        {
            if (number == 0)
            {
                e.Bitvector = NewChild;
                return;
            }

            throw new InvalidOperationException("BvExtract only has one child");

        }

        public static Expr GetChild(this BvExtractExpr e, int number)
        {
            if (number == 0)
                return e.Bitvector;

            throw new InvalidOperationException("BvExtract only has one child");
        }

        // BvConcatExpr
        public static int GetNumberOfChildren(this BvConcatExpr e)
        {
            return 2;
        }

        public static void SetChild(this BvConcatExpr e, int number, Expr NewChild)
        {
            switch (number)
            {
                case 0:
                    e.E0 = NewChild; // Most significant bytes
                    return;
                case 1:
                    e.E1 = NewChild; // Least significant bytes
                    return;
                default:
                    throw new InvalidOperationException("BvConcat only has two children");
            }
        }

        public static Expr GetChild(this BvConcatExpr e, int number)
        {
            switch (number)
            {
                case 0:
                    return e.E0; // Most significant bytes
                case 1:
                    return e.E1;// Least significant bytes
                default:
                    throw new InvalidOperationException("BvConcat only has two children");
            }
        }

        // ForallExpr
        public static int GetNumberOfChildren(this ForallExpr e)
        {
            return 1;
        }

        public static void SetChild(this ForallExpr e, int number, Expr NewChild)
        {
            switch (number)
            {
            case 0:
                e.Body = NewChild;
                return;

            default:
                throw new InvalidOperationException("ForallExpr only has one child");
            }
        }

        public static Expr GetChild(this ForallExpr e, int number)
        {
            switch (number)
            {
            case 0:
                return e.Body;
            default:
                throw new InvalidOperationException("ForallExpr only has one child");
            }
        }

        // ExistsExpr
        public static int GetNumberOfChildren(this ExistsExpr e)
        {
            return 1;
        }

        public static void SetChild(this ExistsExpr e, int number, Expr NewChild)
        {
            switch (number)
            {
            case 0:
                e.Body = NewChild;
                return;

            default:
                throw new InvalidOperationException("ExistsExpr only has one child");
            }
        }

        public static Expr GetChild(this ExistsExpr e, int number)
        {
            switch (number)
            {
            case 0:
                return e.Body;
            default:
                throw new InvalidOperationException("ExistsExpr only has one child");
            }
        }

        // OldExpr
        public static int GetNumberOfChildren(this OldExpr e)
        {
            return 1;
        }

        public static void SetChild(this OldExpr e, int number, Expr NewChild)
        {
            switch (number)
            {
                case 0:
                    e.Expr = NewChild;
                    return;

                default:
                    throw new InvalidOperationException("OldExpr only has one child");
            }
        }

        public static Expr GetChild(this OldExpr e, int number)
        {
            switch (number)
            {
                case 0:
                    return e.Expr;
                default:
                    throw new InvalidOperationException("OldExpr only has one child");
            }
        }
    }
}

