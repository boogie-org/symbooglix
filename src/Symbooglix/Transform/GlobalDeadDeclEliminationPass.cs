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
using System.Linq;
using Microsoft.Boogie;

namespace Symbooglix
{
    namespace Transform
    {
        public class GlobalDeadDeclEliminationPass : IPass
        {
            public GlobalDeadDeclEliminationPass()
            {
            }
            public string GetName()
            {
                return "Global Dead Declaration Elimination Pass";
            }

            public void SetPassInfo(ref PassInfo passInfo)
            {
                return;
            }

            public bool RunOn(Program prog, PassInfo passInfo)
            {
                // Collect used functions and global variables.
                // Note we don't want to consider an axiom as "using" interpreted functions because
                // axioms using interpreted functions aren't (or at least shouldn't be) constraining
                // those interpreted functions. If we considered interpreted functions as being used by
                // axioms then this might prevent those axioms (and uninterpreted functions in those axioms)
                // form being removed.
                var FFV = new FindUsedFunctionAndGlobalVariableVisitor(/*ignoreInterpretedFunctionsInAxioms=*/ true);
                FFV.Visit(prog);

                // Initialise with all declared functions
                var functionsToRemove = new HashSet<Function>(prog.TopLevelDeclarations.OfType<Function>());
                // reduce the set by removing functions used in code
                functionsToRemove.ExceptWith(FFV.FuncsUsedInCode);

                // Initialise with all declared global variables
                var gvsToRemove = new HashSet<Variable>(prog.TopLevelDeclarations.OfType<Variable>());
                // reduce the set by removing variables used in code
                gvsToRemove.ExceptWith(FFV.VarsUsedInCode);

                // We don't Initialise with all declared axioms
                var axiomsToRemove = new HashSet<Axiom>();

                // Compute transitive closure of axiom dependencies.
                // Some axioms may share variables for example
                // axiom e > f;
                // axiom f > g;
                // axiom g > h;
                //
                // if we decide that only variable h is live we need to keep all three axioms
                // which requires that we know how axioms depend on each other
                //
                // An axiom A is directly dependent on axiom B iff they share any common
                // functions or global variables.
                //
                // Axioms can be transitively dependent on each other
                Dictionary<Axiom, HashSet<Axiom>> axiomDeps = new Dictionary<Axiom, HashSet<Axiom>>();
                foreach (var axiom in prog.TopLevelDeclarations.OfType<Axiom>())
                {
                    axiomDeps[axiom] = new HashSet<Axiom>();
                }

                // Compute direct dependencies
                foreach (var axiom in prog.TopLevelDeclarations.OfType<Axiom>())
                {
                    foreach (var otherAxiom in prog.TopLevelDeclarations.OfType<Axiom>().Where( a => a != axiom))
                    {
                        if (axiomDeps[axiom].Contains(otherAxiom))
                            continue;

                        if ( FFV.FuncsUsedInAxiom[axiom].Overlaps( FFV.FuncsUsedInAxiom[otherAxiom]) ||
                             FFV.VarsUsedInAxiom[axiom].Overlaps( FFV.VarsUsedInAxiom[otherAxiom])
                           )
                        {
                            axiomDeps[axiom].Add(otherAxiom);
                            axiomDeps[otherAxiom].Add(axiom);
                        }
                    }
                }

                // For each axiom compute the transistive closure of dependencies by reaching a fixed point for each axiom
                foreach (var axiom in prog.TopLevelDeclarations.OfType<Axiom>())
                {
                    bool setChanged = false;
                    do
                    {
                        var axiomsToAdd = new HashSet<Axiom>();
                        setChanged = false;

                        foreach (var dep in axiomDeps[axiom])
                        {
                            axiomsToAdd.UnionWith(axiomDeps[dep]);
                        }

                        int previousNumberOfDeps = axiomDeps[axiom].Count;
                        axiomDeps[axiom].UnionWith(axiomsToAdd);

                        if (axiomDeps[axiom].Count > previousNumberOfDeps)
                            setChanged = true;

                    } while (setChanged);
                }

                // Work out which axioms to remove
                var axiomsMustKeep = new HashSet<Axiom>();
                foreach (var axiom in prog.TopLevelDeclarations.OfType<Axiom>())
                {
                    var liveVars = new HashSet<Variable>(FFV.VarsUsedInAxiom[axiom]);
                    // Remove the variables (that we plan to remove) from the set so we are only left with live variables
                    liveVars.ExceptWith(gvsToRemove);

                    var liveFuncs = new HashSet<Function>(FFV.FuncsUsedInAxiom[axiom]);
                    // Remove the functions (that we plan to remove) from the set so we are only left with live functions
                    liveFuncs.ExceptWith(functionsToRemove);

                    if (liveVars.Count == 0 && liveFuncs.Count == 0)
                    {
                        axiomsToRemove.Add(axiom);
                    }
                    else
                    {
                        // Can't remove axiom. This means we shouldn't remove any of its dependencies
                        // We can't modify axiomsToRemove directly (i.e. axiomsToRemove.ExceptWith(axiomDeps[axiom]) )
                        // because the dependencies might be added to axiomsToRemove in a later iteration of this loop
                        axiomsMustKeep.UnionWith(axiomDeps[axiom]);
                    }
                }

                // Remove any axioms from the set that we discovered must be kept.
                axiomsToRemove.ExceptWith(axiomsMustKeep);


                // Work out which functions to remove
                var newFunctionsToRemove = new HashSet<Function>(); // can't modify set whilst iterating so write into temp
                foreach (var f in functionsToRemove)
                {
                    if (!FFV.AxiomsUsingFunc.ContainsKey(f))
                    {
                        // no axioms use this function so we can definitely remove it
                        newFunctionsToRemove.Add(f);
                        continue;
                    }
                    var liveAxiomsUsingFunc = new HashSet<Axiom>(FFV.AxiomsUsingFunc[f]);

                    // Compute which live axioms use this function
                    liveAxiomsUsingFunc.ExceptWith(axiomsToRemove);

                    if (liveAxiomsUsingFunc.Count == 0)
                    {
                        // We can remove this function
                        newFunctionsToRemove.Add(f);
                    }
                }
                functionsToRemove = newFunctionsToRemove;

                // Work out which global variables to remove
                var newGvsToRemove = new HashSet<Variable>(); // can't modify the set whilst iterarting so write into temp
                foreach (var gv in gvsToRemove)
                {
                    if (!FFV.AxiomsUsingVar.ContainsKey(gv))
                    {
                        // no axioms use this variable so we can definitely remove it
                        newGvsToRemove.Add(gv);
                        continue;
                    }

                    var liveAxiomsUsingVar = new HashSet<Axiom>(FFV.AxiomsUsingVar[gv]);

                    // compute which live axioms use this variable
                    liveAxiomsUsingVar.ExceptWith(axiomsToRemove);

                    if (liveAxiomsUsingVar.Count == 0)
                    {
                        // We can remove this variable
                        newGvsToRemove.Add(gv);
                    }
                }
                gvsToRemove = newGvsToRemove;

                bool changed = false;

                // Now remove the axioms
                foreach (var axiom in axiomsToRemove)
                {
                    changed = true;
                    Console.Error.WriteLine("Warning removing dead axiom: {0}", axiom.Expr.ToString());
                    prog.RemoveTopLevelDeclaration(axiom);
                }

                // Now remove the functions
                foreach (var f in functionsToRemove)
                {
                    changed = true;
                    Console.Error.WriteLine("Warning removing dead function {0}", f.Name);
                    prog.RemoveTopLevelDeclaration(f);
                }

                // Now remove the globally scoped variables
                foreach (var gv in gvsToRemove)
                {
                    changed = true;
                    Console.Error.WriteLine("Warning removing dead globally scoped variable {0}", gv.Name);
                    prog.RemoveTopLevelDeclaration(gv);
                }

                // FIXME: We need some way of validating the Boogie Program to make sure
                // all function Calls point to top level declared functions and that reference globals
                // are still top level declarations.
                return changed;
            }

            public void Reset()
            {
            }
        }

        class FindUsedFunctionAndGlobalVariableVisitor : ReadOnlyVisitor
        {
            public HashSet<Function> FuncsUsedInCode; // Used in Procedure, Implementations and function bodies
            public HashSet<Variable> VarsUsedInCode; // Used in Procedure, Implementations and function bodies

            // Effectively storing the mapping both ways
            public Dictionary<Function, HashSet<Axiom>> AxiomsUsingFunc;
            public Dictionary<Axiom, HashSet<Function>> FuncsUsedInAxiom;

            public Dictionary<Variable, HashSet<Axiom>> AxiomsUsingVar;
            public Dictionary<Axiom, HashSet<Variable>> VarsUsedInAxiom;

            private bool InAxiom;
            private Axiom CurrentAxiom;
            public readonly bool IgnoreInterpretedFunctionsInAxioms;
            public FindUsedFunctionAndGlobalVariableVisitor(bool ignoreInterpretedFunctionsInAxioms)
            {
                FuncsUsedInCode = new HashSet<Function>();
                VarsUsedInCode = new HashSet<Variable>();

                AxiomsUsingFunc = new Dictionary<Function, HashSet<Axiom>>();
                FuncsUsedInAxiom = new Dictionary<Axiom, HashSet<Function>>();
                AxiomsUsingVar = new Dictionary<Variable, HashSet<Axiom>>();
                VarsUsedInAxiom = new Dictionary<Axiom, HashSet<Variable>>();
                IgnoreInterpretedFunctionsInAxioms = ignoreInterpretedFunctionsInAxioms;

                InAxiom = false;
            }

            public void Clear()
            {
                FuncsUsedInCode.Clear();
                VarsUsedInCode.Clear();

                AxiomsUsingFunc.Clear();
                FuncsUsedInAxiom.Clear();
                AxiomsUsingVar.Clear();
                VarsUsedInAxiom.Clear();
            }

            public override Program VisitProgram(Program node)
            {
                foreach (var tld in node.TopLevelDeclarations)
                {
                    // Don't record top level functions or variables because these are declarations.
                    // We only care about uses of functions or variables
                    if (tld is GlobalVariable || tld is Constant || tld is Function)
                    {
                        continue;
                    }
                    else
                    {
                        Visit(tld);
                    }
                }
                return node;
            }

            public override Axiom VisitAxiom(Axiom node)
            {
                // Entering an Axiom
                InAxiom = true;
                CurrentAxiom = node;

                // Initialise HashSets for this axiom
                if (!FuncsUsedInAxiom.ContainsKey(node))
                    FuncsUsedInAxiom[node] = new HashSet<Function>();

                if (!VarsUsedInAxiom.ContainsKey(node))
                    VarsUsedInAxiom[node] = new HashSet<Variable>();

                var result = base.VisitAxiom(node);

                // Leaving an Axiom
                CurrentAxiom = null;
                InAxiom = false;
                return result;
            }

            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (node.Fun is FunctionCall)
                    VisitFunctionCall(node.Fun as FunctionCall);

                return base.VisitNAryExpr(node);
            }

            public override Function VisitFunction(Function node) {
                Debug.Assert(node != null);
                if (InAxiom) {
                    Debug.Assert(CurrentAxiom != null);

                    if (IgnoreInterpretedFunctionsInAxioms && ExprUtil.AsUninterpretedFunction(node) == null) {
                        // This FunctionCall does not call an uninterpreted function. Therefore it must call an
                        // an interpreted function
                        return node;
                    }

                    if (FuncsUsedInAxiom[CurrentAxiom].Contains(node)) {
                        // We've already visited this function before
                        // in the context of this axiom. So don't visit again.
                        // This means we might travserse the same function
                        // body multiple times in the context of different axioms.
                        // I think that means we'll never get stuck traversing
                        // recursive function bodies but I'm not sure.
                        return node;
                    }

                    // Record the mapping both ways
                    if (!AxiomsUsingFunc.ContainsKey(node)) {
                        AxiomsUsingFunc[node] = new HashSet<Axiom>();
                    }
                    AxiomsUsingFunc[node].Add(CurrentAxiom);

                    // Assume Hash set has already been initialised
                    FuncsUsedInAxiom[CurrentAxiom].Add(node);
                } else {
                    if (FuncsUsedInCode.Contains(node)) {
                        // We've visited this function before in the context
                        // of code so we don't need to add it to `FuncsUsedInCode`
                        // or travserse its body again. Traversing again might
                        // get us stuck in a loop with recursive functions.
                        return node;
                    }
                    FuncsUsedInCode.Add(node);
                }

                // Now if the function has a body traverse that because
                // this function depends on functions that this function calls
                if (node.Body != null) {
                    Visit(node.Body);
                }
                return node;
            }

            public void VisitFunctionCall(FunctionCall node)
            {
                VisitFunction(node.Func);
            }

            public override Variable VisitVariable(Variable node)
            {
                // We only record the Globally scoped variables
                if (!(node is GlobalVariable) && !(node is Constant))
                    return base.VisitVariable(node);

                if (InAxiom)
                {
                    Debug.Assert(CurrentAxiom != null);

                    // Record the mapping both ways
                    if (!AxiomsUsingVar.ContainsKey(node))
                    {
                        AxiomsUsingVar[node] = new HashSet<Axiom>();
                    }
                    AxiomsUsingVar[node].Add(CurrentAxiom);

                    // Assume Hash set has already been initialised
                    VarsUsedInAxiom[CurrentAxiom].Add(node);
                }
                else
                {
                    VarsUsedInCode.Add(node);
                }

                return base.VisitVariable(node);
            }
        }
    }
 
}

