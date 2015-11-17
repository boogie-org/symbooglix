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

        public Constraint GetNegatedConstraint(IExprBuilder builder)
        {
            var that = (Constraint) this.MemberwiseClone();

            // Optimisation:
            // We don't need to recompute (or copy) the set of used UF and variables
            // for that

            // Negate the Condition
            if (!Condition.Type.IsBool)
                throw new ExprTypeCheckException("Cannot negate an expression that is not a bool");

            that.Condition = builder.Not(this.Condition);
            return that;
        }

        private void ComputeUsedVariablesAndUninterpretedFunctions()
        {
            this.InternalUsedVariables = new HashSet<SymbolicVariable>();
            this.InternalUsedUninterpretedFunctions = new HashSet<Function>();
            var fvuf = new FindSymbolicsAndUFsVisitor(this.InternalUsedVariables, this.InternalUsedUninterpretedFunctions);
            fvuf.Visit(Condition);
        }

        // Equality and GetHashCode only care about the constraint
        // they don't care if the Origin is different
        public override bool Equals(object obj)
        {
            if (obj == null)
                return false;

            var other = obj as Constraint;
            if (other == null)
                return false;

            // Try to do quick checks first
            if (InternalUsedVariables.Count != other.InternalUsedVariables.Count)
                return false;

            if (InternalUsedUninterpretedFunctions.Count != other.InternalUsedUninterpretedFunctions.Count)
                return false;

            // Potentially slow comparision
            return ExprUtil.StructurallyEqual(this.Condition, other.Condition);
        }

        public override int GetHashCode()
        {
            return this.Condition.GetHashCode();
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
            var asUFC = ExprUtil.AsUninterpretedFunctionCall(e);
            if (asUFC != null)
            {
                UninterpretedFunctions.Add((asUFC.Fun as FunctionCall).Func);
            }
        }
    }
}

