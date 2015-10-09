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
using System.Linq;

namespace Symbooglix
{
    namespace Transform
    {
        public class UniqueVariableEnforcingPass : IPass
        {
            public HashSet<Axiom> InternalAddedAxioms;
            public IEnumerable<Axiom> AddedAxioms
            {
                get { return InternalAddedAxioms; }
            }

            public UniqueVariableEnforcingPass()
            {
                InternalAddedAxioms = new HashSet<Axiom>();
            }

            public string GetName()
            {
                return "Unique Variable Enforcing Pass";
            }

            public void SetPassInfo(ref PassInfo passInfo)
            {
                return;
            }

            public bool RunOn(Program prog, PassInfo passInfo)
            {
                // We assume that types are uniqued so "GroupBy" works correctly
                var groupedVariables = prog.TopLevelDeclarations.OfType<Constant>().Where( c => c.Unique).GroupBy( c => c.TypedIdent.Type);
                bool changed = false;

                foreach (var pair in groupedVariables)
                {
                    var listOfUniqueVars = pair.ToList();
                    if (listOfUniqueVars.Count > 1)
                    {
                        Expr axiomExpr = null;
                        changed = true;

                        // Create IdentifierExprs
                        Dictionary<Variable, IdentifierExpr> ids = new Dictionary<Variable, IdentifierExpr>();
                        foreach (var uv in listOfUniqueVars)
                            ids.Add(uv, new IdentifierExpr(Token.NoToken, uv));

                        // Create an Expr asserting that all variables are different from each other (pair wise)
                        for (int firstVarIndex = 0; firstVarIndex < listOfUniqueVars.Count -1; ++firstVarIndex)
                        {
                            for (int secondVarIndex = firstVarIndex + 1; secondVarIndex < listOfUniqueVars.Count; ++secondVarIndex)
                            {
                                var firstVar = listOfUniqueVars[firstVarIndex];
                                var secondVar = listOfUniqueVars[secondVarIndex];
                                var notEq = Expr.Neq(ids[firstVar], ids[secondVar]); // FIXME: Use ExprBuilder instead

                                if (axiomExpr == null)
                                    axiomExpr = notEq;
                                else
                                    axiomExpr = Expr.And(axiomExpr, notEq);
                            }
                        }

                        // Create the Axiom
                        var axiom = new Axiom(Token.NoToken, axiomExpr);
                        axiom.AddAttribute("symbooglix_enforce_unique", Expr.True);
                        prog.AddTopLevelDeclaration(axiom);
                        InternalAddedAxioms.Add(axiom);
                        Console.WriteLine("Adding axiom to enforce uniqueness of constant variables of {0} type that use the unique keyword", pair.Key.ToString());
                    }
                }

                return changed;
            }

            public void Reset()
            {
                InternalAddedAxioms.Clear();
            }
        }


    }
}

