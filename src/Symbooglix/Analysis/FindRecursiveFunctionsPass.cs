//------------------------------------------------------------------------------
//                                  Symbooglix
//
//
// Copyright 2014-2015 Daniel Liew
//
// This file is licensed under the 2-Clause BSD license.
// See LICENSE for details.
//------------------------------------------------------------------------------
using Microsoft.Boogie;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;

namespace Symbooglix
{
    public class FindRecursiveFunctionsPass : Transform.IPass
    {
        public HashSet<Function> RecursiveFunctions;

        public FindRecursiveFunctionsPass()
        {
            RecursiveFunctions = new HashSet<Function>();
        }

        public bool RunOn(Program prog, Transform.PassInfo passInfo)
        {
            foreach (var func in prog.TopLevelDeclarations.OfType<Function>())
            {
                var findRecursiveFunctionVisitor = new FindRecursiveFunctionVisitor(RecursiveFunctions);
                findRecursiveFunctionVisitor.Visit(func);
            }
            return false; // This is an Analysis that doesn't modify anything about the Functions
        }

        public string GetName()
        {
            return "Find recursive functions";
        }

        public void SetPassInfo(ref Transform.PassInfo passInfo)
        {
            // No dependencies
            return;
        }

        public void Reset()
        {
            RecursiveFunctions.Clear();
        }
    }

    // This supports looking for mutually recursive functions
    public class FindRecursiveFunctionVisitor : ReadOnlyVisitor
    {
        private List<Function> CallStack;
        public HashSet<Function> RecursiveFunctions;
        private bool LookForMutualRecursion;

        // Allow using an external container to store the found recursiveFunctions
        public FindRecursiveFunctionVisitor(HashSet<Function> recursiveFunctions, bool lookForMutualRecursion= true) 
        { 
            this.RecursiveFunctions = recursiveFunctions;
            this.LookForMutualRecursion = lookForMutualRecursion;
            this.CallStack = new List<Function>();
        }

        public FindRecursiveFunctionVisitor(bool lookForMutualRecursion=true) : this(new HashSet<Function>(), lookForMutualRecursion)
        {
        }

        private bool IsInCallStack(Function func)
        {
            return CallStack.Contains(func);
        }
            
        public override Function VisitFunction(Function node)
        {
            // FIXME we should factor this test into a utility function
            // because its needed in many places.
            // SMTLIBv2 bvbuiltins can't be recursive
            if (QKeyValue.FindStringAttribute(node.Attributes, "bvbuiltin") != null)
                return node;

            if (QKeyValue.FindStringAttribute(node.Attributes, "builtin") != null)
                return node;

            // Pop on to stack
            CallStack.Add(node);
            if (node.Body != null)
            {
                base.Visit(node.Body);
            }
                
            // Explore definition axiom for the form (forall args :: func(args) <==> expr)
            if (node.DefinitionAxiom != null)
            {
                Debug.Assert(node.DefinitionAxiom.Expr is ForallExpr, "Function defintion axiom is not a forall!");
                var forall = node.DefinitionAxiom.Expr as ForallExpr;
                Debug.Assert(forall.Dummies.Count == node.InParams.Count, "Number of arguments do not match");
                Debug.Assert(forall.Body is NAryExpr, "forall body is not an NAryExpr");

                var equality = forall.Body as NAryExpr;
                Debug.Assert(equality.Fun is BinaryOperator, "Forall body is not a BinaryOperator");
                var binaryOperator = equality.Fun as BinaryOperator;
                Debug.Assert(binaryOperator.Op == BinaryOperator.Opcode.Iff || binaryOperator.Op == BinaryOperator.Opcode.Eq,
                             "Binary Operator is not == or <==>");
                             
                // Check == or <==> applies to this function
                // We assume the function is on the lhs
                Debug.Assert(equality.Args[0] is NAryExpr, "lhs is not NAryExpr");
                var lhs = equality.Args[0] as NAryExpr;

                // May need to step through type coercions
                NAryExpr shouldBeFunctionCall = lhs;
                while (shouldBeFunctionCall.Fun is TypeCoercion)
                {
                    Debug.Assert(lhs.Args[0] is NAryExpr, "Hit non NAryExpr whilst traversing TypeCoercion");
                    shouldBeFunctionCall = lhs.Args[0] as NAryExpr;
                }


                Debug.Assert(shouldBeFunctionCall.Fun is FunctionCall, "LHS is not a FunctionCall");
                var lhsFuncCall = shouldBeFunctionCall.Fun as FunctionCall;
                Debug.Assert(lhsFuncCall.Func.Equals(node), "Axiom does not apply to function " + node.Name);

                // The rhs is the Function Expr
                base.Visit(equality.Args[1]);
            }

            // Pop from stack
            CallStack.Remove(node);
            return node;
        }
            
        public override Expr VisitNAryExpr(NAryExpr node)
        {
            if (! (node.Fun is FunctionCall))
                return base.VisitNAryExpr(node);

            var FC = node.Fun as FunctionCall;

            // Check if we have already called this in the current callstack
            if (IsInCallStack(FC.Func))
            {
                // Found recursion.
                RecursiveFunctions.Add(FC.Func);

                // We shouldn't go deeper else we get stuck in an infinite loop
                return node;
            }
            else
            {
                if (LookForMutualRecursion)
                    VisitFunction(FC.Func);

                // Explore arguments too
                VisitExprSeq(node.Args);
            }

            return node;
        }
    }
}

