using System;
using Microsoft.Boogie;
using System.Collections.Generic;
using System.Diagnostics;

namespace Symbooglix
{

    public class Constraint
    {
        public Expr Condition { get; private set;}
        public ProgramLocation Origin { get; private set;}

        // Hide the implementation of the Set
        private HashSet<SymbolicVariable> InternalUsedVariables;
        public ISet<SymbolicVariable> UsedVariables { get { return InternalUsedVariables; } }

        private HashSet<Function> InternalUsedUninterpretedFunctions;
        public ISet<Function> UsedUninterpretedFunctions { get { return InternalUsedUninterpretedFunctions; } }

        public Constraint(Expr condition)
        {
            Condition = condition;
            Debug.Assert(condition.ShallowType.IsBool, "Constraint must be a boolean expression!");
            Origin = null;
            ComputeUsedVariablesAndUninterpretedFunctions();
        }

        public Constraint(Expr condition, ProgramLocation location) : this(condition)
        {
            Debug.Assert(location != null);
            Origin = location;
            ComputeUsedVariablesAndUninterpretedFunctions();
        }

        public Constraint GetNegatedConstraint()
        {
            var that = (Constraint) this.MemberwiseClone();

            // Optimisation:
            // We don't need to recompute (or copy) the set of used UF and variables
            // for that

            // Negate the Condition
            if (!Condition.Type.IsBool)
                throw new ExprTypeCheckException("Cannot negate an expression that is not a bool");

            // FIXME: We should be using an IExprBuilder
            that.Condition = Expr.Not(this.Condition);
            return that;
        }

        private void ComputeUsedVariablesAndUninterpretedFunctions()
        {
            this.InternalUsedVariables = new HashSet<SymbolicVariable>();
            this.InternalUsedUninterpretedFunctions = new HashSet<Function>();
            var fvuf = new FindSymbolicsAndUFsVisitor(this.InternalUsedVariables, this.InternalUsedUninterpretedFunctions);
            fvuf.Visit(Condition);
        }
    }

    class ConstraintInHashSetCompare : IEqualityComparer<Constraint>
    {
        public bool Equals(Constraint x, Constraint y)
        {
            // Potentially slow comparision
            return ExprUtil.StructurallyEqual(x.Condition, y.Condition);
        }

        public int GetHashCode(Constraint obj)
        {
            return obj.Condition.GetHashCode();
        }
    }

    class FindSymbolicsAndUFsVisitor
    {
        public HashSet<SymbolicVariable> SymbolicVariables;
        public HashSet<Function> UninterpretedFunctions;
        public FindSymbolicsAndUFsVisitor(HashSet<SymbolicVariable> symVars, HashSet<Function> ufs)
        {
            SymbolicVariables = symVars;
            UninterpretedFunctions = ufs;
        }

        public FindSymbolicsAndUFsVisitor() : this(new HashSet<SymbolicVariable>(), new HashSet<Function>())
        {
        }

        // Non-recursive version that records expressions it's visited because we might have a dag
        public virtual void Visit(Expr e)
        {
            // We only do reference equality because the equal comparision is recursive and could cause a stackoverflow.
            var visitedNodes = new HashSet<Expr>(new ExprReferenceCompare());

            // Visit DFS pre-order
            var queue = new Queue<Expr>();
            queue.Enqueue(e);

            do
            {
                // Pop off node from queue
                var node = queue.Dequeue();

                if (visitedNodes.Contains(node))
                {
                    // Don't traverse this node. We've seen it before
                    continue;
                }

                // Add node's children to the queue
                for (int index=0; index < node.GetNumberOfChildren(); ++index)
                {
                    queue.Enqueue(node.GetChild(index));
                }

                // handle node
                VisitNode(node);
                visitedNodes.Add(node);

            } while (queue.Count > 0);
            visitedNodes.Clear();
        }

        protected virtual void VisitNode(Expr e)
        {
            // Collect Symbolic Variables
            var asId= e as IdentifierExpr;
            if (asId != null)
            {
                if (asId.Decl is BoundVariable)
                {
                    // These may appear if we are in a quantified expression
                    return;
                }

                if (!( asId.Decl is SymbolicVariable ))
                    throw new Exception("id not pointing to symbolic variable");

                SymbolicVariables.Add(asId.Decl as SymbolicVariable);
                return;
            }

            // Collect uninterpreted functions
            var asFC = ExprUtil.AsFunctionCall(e);
            if (asFC != null)
            {
                var FC = asFC.Fun as FunctionCall;

                // Don't collect SMTLIBv2 functions
                if (QKeyValue.FindStringAttribute(FC.Func.Attributes, "bvbuiltin") != null)
                    return;

                // Don't collect other builtins
                if (QKeyValue.FindStringAttribute(FC.Func.Attributes, "builtin") != null)
                    return;

                UninterpretedFunctions.Add(FC.Func);
            }
        }
    }
}

