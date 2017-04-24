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
using System.Collections.Generic;
using System.Diagnostics;
using Microsoft.Boogie;

namespace Symbooglix
{
    public class BuilderDuplicator : Duplicator
    {
        public IExprBuilder Builder;
        public BuilderDuplicator(IExprBuilder builder)
        {
            Debug.Assert(builder != null);
            Builder = builder;
        }

        public override Expr VisitBvConcatExpr(BvConcatExpr node)
        {
            var MSBCopy = this.Visit(node.E0) as Expr;
            var LSBCopy = this.Visit(node.E1) as Expr;
            var newNode = Builder.BVCONCAT(MSBCopy, LSBCopy);
            Debug.Assert(MSBCopy != null);
            Debug.Assert(LSBCopy != null);
            Debug.Assert(newNode != null);
            return newNode;
        }

        public override Expr VisitCodeExpr(CodeExpr node)
        {
            throw new NotImplementedException();
        }

        public override Expr VisitExistsExpr(ExistsExpr node)
        {
            var bodyCopy = this.Visit(node.Body) as Expr;
            Debug.Assert(bodyCopy != null);
            var freeVars = new List<Variable>(node.Dummies);
            var newTriggers = this.VisitTrigger(node.Triggers);
            var newNode = Builder.Exists(freeVars, bodyCopy, newTriggers);
            Debug.Assert(newNode != null);
            return newNode;
        }

        public override Trigger VisitTrigger(Trigger node)
        {
            if (node == null)
                return null;

            return base.VisitTrigger(node);
        }

        public override Expr VisitBvExtractExpr(BvExtractExpr node)
        {
            var bvCopy = this.Visit(node.Bitvector) as Expr;
            var newNode = Builder.BVEXTRACT(bvCopy, node.End, node.Start);
            Debug.Assert(bvCopy != null);
            Debug.Assert(newNode != null);
            return newNode;
        }

        public override Expr VisitExpr(Expr node)
        {
            var newNode = this.Visit(node) as Expr;
            Debug.Assert(newNode != null);
            return newNode;
        }

        public override Expr VisitForallExpr(ForallExpr node)
        {
            var bodyCopy = this.Visit(node.Body) as Expr;
            Debug.Assert(bodyCopy != null);
            var freeVars = new List<Variable>(node.Dummies);
            var newTriggers = this.VisitTrigger(node.Triggers);
            var newNode = Builder.ForAll(freeVars, bodyCopy, newTriggers);
            Debug.Assert(newNode != null);
            return newNode;
        }

        public override Expr VisitLambdaExpr(LambdaExpr node)
        {
            throw new NotImplementedException();
        }

        public override Function VisitFunction(Function node)
        {
            throw new NotSupportedException("This should never be reached");
        }

        public override Expr VisitLiteralExpr(LiteralExpr node)
        {
            if (node.isBool)
            {
                return (Expr) Builder.ConstantBool(node.asBool);
            }
            else if (node.isBigNum)
            {
                return Builder.ConstantInt(node.asBigNum.ToBigInteger);
            }
            else if (node.isBigDec)
            {
                return Builder.ConstantReal(node.asBigDec);
            }
            else if (node.isBvConst)
            {
                var bv = node.asBvConst;
                return Builder.ConstantBV(bv.Value.ToBigInteger, bv.Bits);
            }
            else
            {
                throw new NotSupportedException("Unknown LiteralExpr type");
            }
        }

        protected Expr HandleBvBuiltIns(FunctionCall fc, string builtin, List<Expr> newArgs)
        {
            Debug.Assert(builtin.Length > 0);

            // We grab for first word because the bvbuiltin
            // might be "zeroextend 16", we don't care about the number
            string firstWord = builtin.Split(' ')[0];
            Debug.Assert(firstWord.Length > 0);

            // Handle `(_ zero_extend x)` and `(_ sign_extend x)` style builtins
            if (firstWord.StartsWith("(_")) {
                var words = builtin.Split(' ');
                if (words.Length < 2) {
                    throw new ArgumentException("Malformed bvbuiltin name \"" + builtin + "\"");
                }
                firstWord = words[1];
            }

            int retWidth = 0;
            switch (firstWord)
            {
                // arithmetic
                case "bvadd":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVADD(newArgs[0], newArgs[1]);
                case "bvsub":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVSUB(newArgs[0], newArgs[1]);
                case "bvmul":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVMUL(newArgs[0], newArgs[1]);
                case "bvudiv":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVUDIV(newArgs[0], newArgs[1]);
                case "bvurem":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVUREM(newArgs[0], newArgs[1]);
                case "bvsdiv":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVSDIV(newArgs[0], newArgs[1]);
                case "bvsrem":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVSREM(newArgs[0], newArgs[1]);
                case "bvsmod":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVSMOD(newArgs[0], newArgs[1]);
                case "sign_extend":
                    Debug.Assert(newArgs.Count == 1);
                    Debug.Assert(fc.Func.OutParams.Count == 1);
                    retWidth = fc.Func.OutParams[0].TypedIdent.Type.BvBits;
                    return Builder.BVSEXT(newArgs[0], retWidth);
                case "zero_extend":
                    Debug.Assert(newArgs.Count == 1);
                    Debug.Assert(fc.Func.OutParams.Count == 1);
                    retWidth = fc.Func.OutParams[0].TypedIdent.Type.BvBits;
                    return Builder.BVZEXT(newArgs[0], retWidth);
                case "bvneg":
                    Debug.Assert(newArgs.Count == 1);
                    return Builder.BVNEG(newArgs[0]);
                // bitwise logical
                case "bvand":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVAND(newArgs[0], newArgs[1]);
                case "bvor":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVOR(newArgs[0], newArgs[1]);
                case "bvnot":
                    Debug.Assert(newArgs.Count == 1);
                    return Builder.BVNOT(newArgs[0]);
                case "bvxor":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVXOR(newArgs[0], newArgs[1]);

                    // shift
                case "bvshl":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVSHL(newArgs[0], newArgs[1]);
                case "bvlshr":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVLSHR(newArgs[0], newArgs[1]);
                case "bvashr":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVASHR(newArgs[0], newArgs[1]);

                    // Comparison
                case "bvult":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVULT(newArgs[0], newArgs[1]);
                case "bvule":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVULE(newArgs[0], newArgs[1]);
                case "bvugt":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVUGT(newArgs[0], newArgs[1]);
                case "bvuge":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVUGE(newArgs[0], newArgs[1]);
                case "bvslt":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVSLT(newArgs[0], newArgs[1]);
                case "bvsle":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVSLE(newArgs[0], newArgs[1]);
                case "bvsgt":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVSGT(newArgs[0], newArgs[1]);
                case "bvsge":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.BVSGE(newArgs[0], newArgs[1]);
                default:
                    throw new NotImplementedException("\"" + firstWord + "\" bvbuiltin not supported!");
            }
        }

        protected Expr HandleBuiltIns(FunctionCall fc, string builtin, List<Expr> newArgs)
        {
            // We support very few builtins here. People shouldn't be using them
            switch (builtin)
            {
                case "div":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.Div(newArgs[0], newArgs[1]);
                case "mod":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.Mod(newArgs[0], newArgs[1]);
                case "rem":
                    Debug.Assert(newArgs.Count == 2);
                    return Builder.Rem(newArgs[0], newArgs[1]);
                default:
                    throw new NotImplementedException("Builtin \"" + builtin + "\" not supported");
            }
        }

        public override Expr VisitNAryExpr(NAryExpr node)
        {
            // Need to duplicate arguments first (doing post order traversal)
            var newArgs = new List<Expr>();
            foreach (var oldExpr in node.Args)
            {
                var newExpr = (Expr) this.Visit(oldExpr);
                newArgs.Add(newExpr);
            }

            // Now can finally duplicate this node now we've done our children

            if (node.Fun is FunctionCall)
            {
                var FC = (FunctionCall) node.Fun;
                string bvbuiltin = QKeyValue.FindStringAttribute(FC.Func.Attributes, "bvbuiltin");
                if (bvbuiltin != null)
                {
                    return HandleBvBuiltIns(FC, bvbuiltin, newArgs);
                }
                else
                {
                    string builtin = QKeyValue.FindStringAttribute(FC.Func.Attributes, "builtin");
                    if (builtin != null)
                        return HandleBuiltIns(FC, builtin, newArgs);
                }
                // Not a builtin so treat as uninterpreted function call
                return Builder.UFC(FC, newArgs.ToArray());
            }
            else if (node.Fun is UnaryOperator)
            {
                var U = (UnaryOperator) node.Fun;
                Debug.Assert(newArgs.Count == 1);
                switch (U.Op)
                {
                    case UnaryOperator.Opcode.Neg:
                        return Builder.Neg(newArgs[0]);
                    case UnaryOperator.Opcode.Not:
                        return Builder.Not(newArgs[0]);
                    default:
                        throw new NotImplementedException("Unary operator not supported");
                }
            }
            else if (node.Fun is BinaryOperator)
            {
                var B = (BinaryOperator) node.Fun;
                Debug.Assert(newArgs.Count == 2);
                switch (B.Op)
                {
                // Integer or Real number operators
                    case BinaryOperator.Opcode.Add:
                        return Builder.Add(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Sub:
                        return Builder.Sub(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Mul:
                        return Builder.Mul(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Div:
                        return Builder.Div(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Mod:
                        return Builder.Mod(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.RealDiv:
                        return Builder.RealDiv(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Pow:
                        return Builder.Pow(newArgs[0], newArgs[1]);

                // Comparision operators
                    case BinaryOperator.Opcode.Eq:
                        return Builder.Eq(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Neq:
                        return Builder.NotEq(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Gt:
                        return Builder.Gt(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Ge:
                        return Builder.Ge(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Lt:
                        return Builder.Lt(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Le:
                        return Builder.Le(newArgs[0], newArgs[1]);

                // Bool operators
                    case BinaryOperator.Opcode.And:
                        return Builder.And(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Or:
                        return Builder.Or(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Imp:
                        return Builder.Imp(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Iff:
                        return Builder.Iff(newArgs[0], newArgs[1]);
                    case BinaryOperator.Opcode.Subtype:
                        throw new NotImplementedException("SubType binary operator support not implemented");
                    default:
                        throw new NotSupportedException("Binary operator" + B.Op.ToString() + "not supported!");

                }
            }
            else if (node.Fun is MapStore)
            {
                Debug.Assert(newArgs.Count >= 3);
                // FIXME: We're probably making too many lists/arrays here
                var map = newArgs[0];
                var value = newArgs[newArgs.Count - 1]; // Last argument is value to store
                var indices = new List<Expr>();
                for (int index = 1; index < newArgs.Count - 1; ++index)
                {
                    indices.Add(newArgs[index]);
                }
                Debug.Assert(indices.Count + 2 == newArgs.Count);
                return Builder.MapStore(map, value, indices.ToArray());
            }
            else if (node.Fun is MapSelect)
            {
                // FIXME: We're probably making too many lists/arrays here
                Debug.Assert(newArgs.Count >= 2);
                var map = newArgs[0];
                var indices = new List<Expr>();
                for (int index = 1; index < newArgs.Count; ++index)
                {
                    indices.Add(newArgs[index]);
                }
                Debug.Assert(indices.Count + 1 == newArgs.Count);
                return Builder.MapSelect(map, indices.ToArray());
            }
            else if (node.Fun is IfThenElse)
            {
                Debug.Assert(newArgs.Count == 3);
                return Builder.IfThenElse(newArgs[0], newArgs[1], newArgs[2]);
            }
            else if (node.Fun is TypeCoercion)
            {
                // FIXME: Add support for this in the builder
                // I don't want to put this into the IExprBuilder until I know
                // exactly how this operator works and how it should be type checked
                var immutableTC = new NAryExpr(Token.NoToken, node.Fun, newArgs, /*immutable=*/true);
                immutableTC.Type = node.Type;
                return immutableTC;
            }
            else if (node.Fun is ArithmeticCoercion)
            {
                Debug.Assert(newArgs.Count == 1);
                var ac = node.Fun as ArithmeticCoercion;
                return Builder.ArithmeticCoercion(ac.Coercion, newArgs[0]);
            }

            throw new NotSupportedException("Unsupported NAryExpr");
        }

        public override Expr VisitOldExpr(OldExpr node)
        {
            var newArg = (Expr) this.Visit(node.Expr);
            return Builder.Old(newArg);
        }

        public override Expr VisitIdentifierExpr(IdentifierExpr node)
        {
            // FIXME: This needs to moved out if this class is going to be moved to Boogie's codebase.
            if (node.Decl is SymbolicVariable)
            {
                return ( node.Decl as SymbolicVariable ).Expr;
            }
            return Builder.Identifier(node.Decl);
        }
    }
}

