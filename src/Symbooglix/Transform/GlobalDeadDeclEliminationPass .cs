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
                // Collect used functions and global variables
                var FFV = new FindUsedFunctionAndGlobalVariableVisitor();
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
                // Code cannot use axioms so we can't reduce the set

                // Work out which axioms to remove
                foreach (var axiom in prog.TopLevelDeclarations.OfType<Axiom>())
                {
                    var liveVars = new HashSet<Variable>();
                    var liveFuncs = new HashSet<Function>();

                    if (FFV.VarsUsedInAxiom.ContainsKey(axiom))
                        liveVars.UnionWith(FFV.VarsUsedInAxiom[axiom]);

                    if (FFV.FuncsUsedInAxiom.ContainsKey(axiom))
                        liveFuncs.UnionWith(FFV.FuncsUsedInAxiom[axiom]);

                    // Remove the variables that we plan to remove from the set so we are only left with live variables
                    liveVars.ExceptWith(gvsToRemove);

                    // Remove the functions that we plan to remove from the set so we are only left with live functions
                    liveFuncs.ExceptWith(functionsToRemove);

                    if (liveVars.Count == 0 && liveFuncs.Count == 0)
                        axiomsToRemove.Add(axiom);
                }

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
                    Console.Error.WriteLine("Warning removing dead globally scoped varaible {0}", gv.Name);
                    prog.RemoveTopLevelDeclaration(gv);
                }

                // FIXME: We need some way of validating the Boogie Program to make sure
                // all function Calls point to top level declared functions
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
            public FindUsedFunctionAndGlobalVariableVisitor()
            {
                FuncsUsedInCode = new HashSet<Function>();
                VarsUsedInCode = new HashSet<Variable>();

                AxiomsUsingFunc = new Dictionary<Function, HashSet<Axiom>>();
                FuncsUsedInAxiom = new Dictionary<Axiom, HashSet<Function>>();
                AxiomsUsingVar = new Dictionary<Variable, HashSet<Axiom>>();
                VarsUsedInAxiom = new Dictionary<Axiom, HashSet<Variable>>();

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
                    if (tld is Function)
                    {
                        // We need to visit the function body if it has one because it may reference
                        // other functions
                        var f = tld as Function;
                        if (f.Body != null)
                            Visit(f.Body);

                        continue;
                    }
                    else if (tld is GlobalVariable || tld is Constant)
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
                var result = base.VisitAxiom(node);
                CurrentAxiom = null;
                // Leaving an Axiom
                InAxiom = false;
                return result;
            }

            public override Expr VisitNAryExpr(NAryExpr node)
            {
                if (node.Fun is FunctionCall)
                    VisitFunctionCall(node.Fun as FunctionCall);

                return base.VisitNAryExpr(node);
            }

            public void VisitFunctionCall(FunctionCall node)
            {
                Debug.Assert(node.Func != null);
                if (InAxiom)
                {
                    Debug.Assert(CurrentAxiom != null);

                    // Record the mapping both ways
                    if (!AxiomsUsingFunc.ContainsKey(node.Func))
                    {
                        AxiomsUsingFunc[node.Func] = new HashSet<Axiom>();
                    }
                    AxiomsUsingFunc[node.Func].Add(CurrentAxiom);

                    if (!FuncsUsedInAxiom.ContainsKey(CurrentAxiom))
                    {
                        FuncsUsedInAxiom[CurrentAxiom] = new HashSet<Function>();
                    }
                    FuncsUsedInAxiom[CurrentAxiom].Add(node.Func);
                }
                else
                {
                    FuncsUsedInCode.Add(node.Func);
                }

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

                    if (!VarsUsedInAxiom.ContainsKey(CurrentAxiom))
                    {
                        VarsUsedInAxiom[CurrentAxiom] = new HashSet<Variable>();
                    }
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

