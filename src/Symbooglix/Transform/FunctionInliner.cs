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
using System.Diagnostics;
using System.Collections.Generic;
using System.Linq;

namespace Symbooglix
{
    namespace Transform
    {
        public class FunctionInliningPass : IPass
        {
            private Predicate<Function> Condition;

            // Inling based on some arbitary predicate
            public FunctionInliningPass(Predicate<Function> condition)
            {
                this.Condition = condition;
            }

            public void Reset()
            {
            }

            // The default Inliner inlines function marked with the standard attribute
            public FunctionInliningPass() : this( f => QKeyValue.FindBoolAttribute(f.Attributes,"inline"))
            {

            }

            public bool RunOn(Program prog, PassInfo passInfo)
            {
                var functionInlingVisitor = new FunctionInlingVisitor(Condition);

                // Apply to axioms
                foreach (var axiom in prog.TopLevelDeclarations.OfType<Axiom>())
                {
                    functionInlingVisitor.Visit(axiom);
                }

                // Apply to each Procedure's requires and ensures
                foreach (var procedure in prog.TopLevelDeclarations.OfType<Procedure>())
                {
                    foreach (var ensures in procedure.Ensures)
                    {
                        functionInlingVisitor.Visit(ensures);
                    }

                    foreach (var requires in procedure.Requires)
                    {
                        functionInlingVisitor.Visit(requires);
                    }
                }

                // Apply to functions too, is this correct??
                foreach (var function in prog.TopLevelDeclarations.OfType<Function>())
                {
                    if (function.Body != null)
                    {
                        function.Body = functionInlingVisitor.Visit(function.Body) as Expr;
                    }
                }

                // Apply to Commands in basic blocks
                foreach (var basicBlock in prog.Blocks())
                {
                    functionInlingVisitor.Visit(basicBlock);
                }
                    
                return functionInlingVisitor.InlineCounter > 0;
            }

            public string GetName()
            {
                return "Function inliner";
            }

            public void SetPassInfo(ref PassInfo passInfo)
            {
                return;
            }
        }

        public class FunctionInlingVisitor : StandardVisitor
        {
            private Predicate<Function> Condition;
            public int InlineCounter
            {
                get;
                private set;
            }
            public FunctionInlingVisitor(Predicate<Function> condition)
            {
                this.Condition = condition;
                InlineCounter = 0;
            }

            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (!(node.Fun is FunctionCall))
                    return base.VisitNAryExpr(node);

                var FC = node.Fun as FunctionCall;

                // Can't inline SMTLIBv2 functions
                if (QKeyValue.FindStringAttribute(FC.Func.Attributes, "bvbuiltin") != null)
                    return base.VisitNAryExpr(node);
                    
                if (Condition(FC.Func))
                {
                    if (FC.Func.Body == null)
                        throw new InvalidOperationException("Can't inline a function without a body");

                    // Compute mapping
                    var varToExprMap = new Dictionary<Variable,Expr>();
                    foreach (var parameterArgumentPair in FC.Func.InParams.Zip(node.Args))
                    {
                        varToExprMap.Add(parameterArgumentPair.Item1, parameterArgumentPair.Item2);
                    }

                    // Using Closure :)
                    Substitution sub = delegate(Variable v)
                    {
                        try
                        {
                            return varToExprMap[v];
                        }
                        catch (KeyNotFoundException)
                        {
                            // The substituter seems to expect null being
                            // returned if we don't want to change the variable
                            return null;
                        }
                    };
               
                    // Return the Function expression with variables substituted for function arguments.
                    // This is basically inling
                    ++InlineCounter;
                    var result= Substituter.Apply(sub, FC.Func.Body);

                    // Make sure we visit the result because it may itself contain function calls
                    return (Expr) base.Visit(result);
                }
                else
                    return base.VisitNAryExpr(node);
            }
        }
    }
}

