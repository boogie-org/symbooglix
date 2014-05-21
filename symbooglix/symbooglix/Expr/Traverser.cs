using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;

namespace symbooglix
{
    public abstract class Traverser
    {
        public struct Action
        {
            public enum NextTraversalAction
            {
                CONTINUE,
                HALT // Do replacement if supported then halt traversal
            }

            public NextTraversalAction Next;
            public Expr ReplacementNode;

            static public Action ContinueTraversal(Expr ReplacementNode)
            {
                Action action;
                action.Next = NextTraversalAction.CONTINUE;
                action.ReplacementNode = ReplacementNode;
                return action;
            }


            static public Action HaltTraversal(Expr ReplacementNode)
            {
                Action action;
                action.Next = NextTraversalAction.HALT;
                action.ReplacementNode = ReplacementNode;
                return action;
            }
        }

        protected IExprVisitor Visitor;

        public Traverser(IExprVisitor Visitor)
        {
            this.Visitor = Visitor;
        }

        public abstract void Traverse(Expr root);

        protected Action Visit(Expr e)
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

        protected Action HandleNAry(NAryExpr e)
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
                    // Real number operators
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
                        throw new NotImplementedException("Boolean operator not supported!");

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

            throw new NotImplementedException("NAry not handled!");
        }

        protected Action HandlerBvBuiltIns(NAryExpr e, string builtin)
        {
            switch (builtin)
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
                    throw new NotImplementedException(builtin + " bvbuiltin not supported!");
            }
        }
    }

    public class DFSPostOrderTraverser : Traverser
    {
        public DFSPostOrderTraverser(IExprVisitor visitor) : base(visitor)
        {

        }

        // So we pass by value
        struct ExprNodeInfo
        {
            public Expr node;
            public Expr parent;
            public int childNumber;
        }

        public override void Traverse(Expr root)
        {
            // The approach we use is to compute pre-order (Right-left visiting of children)
            // DFS traversal. We also record the parent of each node so we can do tree rewritting
            // if the visitor requests this.
            //
            // Once we have this list we can walk it backwards to do DFS post-order (left-right visiting of children)
            // traversal.
            if (root == null)
                throw new ArgumentNullException("root cannot be null");

            var preOrderRL = new List<ExprNodeInfo>();

            // Do DFS pre-order (RL)
            var queue = new Stack<ExprNodeInfo>();
            ExprNodeInfo info;
            info.parent = null;
            info.node = root;
            info.childNumber = 0;
            queue.Push(info);

            while (queue.Count != 0)
            {
                var head = queue.Pop();
                preOrderRL.Add(head);

                // Add children in LR order to queue (when we pop we'll do RL)
                for (int index = 0; index < head.node.GetNumberOfChildren(); ++index)
                {
                    info.parent = head.node;
                    info.node = head.node.GetChild(index);
                    info.childNumber = index;
                    queue.Push(info);
                }
            }

            // Phew! We can now post order traversal. Just walk the list backwards
            for (int index = preOrderRL.Count - 1; index >= 0; --index)
            {
                ExprNodeInfo nodeToVisitInfo = preOrderRL[index];
                Action action = Visit(nodeToVisitInfo.node);

                if (action.ReplacementNode != nodeToVisitInfo.node)
                {
                    // We are mutating the tree
                    Debug.WriteLine("Mutating tree: '{0}' => '{1}'", nodeToVisitInfo.node, action.ReplacementNode);
                    nodeToVisitInfo.parent.SetChild(nodeToVisitInfo.childNumber, action.ReplacementNode);
                }

                if (action.Next == Action.NextTraversalAction.HALT)
                    break;
            }

        }
    }
}

