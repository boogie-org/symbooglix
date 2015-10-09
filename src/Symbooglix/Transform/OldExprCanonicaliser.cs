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
using Microsoft.Boogie;
using System.Linq;

namespace Symbooglix
{
    namespace Transform
    {
        /// <summary>
        /// Old expr canonicaliser.
        ///
        /// This pass distributes OldExpr used in the program so
        /// that they only apply to Global Variables (i.e. the leaf nodes)
        ///
        /// e.g. assert old( (2 + 4) * g) ==> assert (2 + 4)* old(g)
        ///
        /// assert old(old(old( 2 + g))) ==> assert 2 + old(g)
        /// </summary>
        public class OldExprCanonicaliser : IPass
        {
            // FIXME: Do we really need this Dictionary? We can just get what we want from the metadata.
            public IDictionary<Procedure, IList<GlobalVariable>> GlobalsInsideOldExprUsedByProcedure =  new Dictionary<Procedure, IList<GlobalVariable>>();
            public IDictionary<Implementation, IList<GlobalVariable>> GlobalsInsideOldExprUsedByImpl = new Dictionary<Implementation, IList<GlobalVariable>>();
            private bool AnnotateProceduresAndImplementations;

            public OldExprCanonicaliser(bool annotateProceduresAndImplementations = true)
            {
                this.AnnotateProceduresAndImplementations = annotateProceduresAndImplementations;
            }

            public void Reset()
            {
                GlobalsInsideOldExprUsedByProcedure.Clear();
                GlobalsInsideOldExprUsedByImpl.Clear();
            }

            public bool RunOn(Program prog, PassInfo passInfo)
            {
                var canonicaliser = new OldExprCanonicaliserVisitor();
                bool changed = false;
                foreach (var proc in prog.TopLevelDeclarations.OfType<Procedure>())
                {
                    canonicaliser.Visit(proc);
                    var GVs = new List<GlobalVariable>();

                    GVs.AddRange(canonicaliser.GlobalsInsideOldExpr);
                    GlobalsInsideOldExprUsedByProcedure[proc] = GVs;

                    if (AnnotateProceduresAndImplementations)
                    {
                        // Add as metadata for easy retrival during execution
                        proc.SetMetadata<IList<GlobalVariable>>((int) Annotation.AnnotationIndex.GLOBALS_USED_IN_OLD_EXPR, GVs);
                    }

                    if (GVs.Count > 0)
                        changed = true;

                    // Clear the recorded globals for next iteration
                    canonicaliser.ResetGlobals();
                }

                foreach (var impl in prog.TopLevelDeclarations.OfType<Implementation>())
                {
                    // Note this will Visit the implementation and the corresponding procedure
                    canonicaliser.Visit(impl);
                    var GVs = new List<GlobalVariable>();

                    GVs.AddRange(canonicaliser.GlobalsInsideOldExpr);
                    GlobalsInsideOldExprUsedByImpl[impl] = GVs;

                    if (AnnotateProceduresAndImplementations)
                    {
                        // Add as metadata for easy retrival during execution
                        impl.SetMetadata<IList<GlobalVariable>>((int) Annotation.AnnotationIndex.GLOBALS_USED_IN_OLD_EXPR, GVs);
                    }

                    if (GVs.Count > 0)
                        changed = true;

                    // Clear the recorded globals for next iteration
                    canonicaliser.ResetGlobals();
                }

                return changed;
            }

            public string GetName()
            {
                return "OldExprCanonicaliser";
            }

            public void SetPassInfo(ref PassInfo passInfo)
            {
                return;
            }
        }

        public class OldExprCanonicaliserVisitor : StandardVisitor
        {
            public HashSet<GlobalVariable> GlobalsInsideOldExpr = new HashSet<GlobalVariable>();

            public void ResetGlobals()
            {
                GlobalsInsideOldExpr.Clear();
            }

            private bool InOldExpr = false;

            public override Expr VisitIdentifierExpr(IdentifierExpr node)
            {
                // Distribute OldExpr to Global Variable leaf nodes only
                if (InOldExpr && node.Decl is GlobalVariable)
                {
                    GlobalsInsideOldExpr.Add(node.Decl as GlobalVariable);
                    return new OldExpr(Token.NoToken, node);
                }

                return base.VisitIdentifierExpr(node);
            }

            public override Expr VisitOldExpr(OldExpr node)
            {
                InOldExpr = true;
                // Go into OldExpr
                var result = base.VisitOldExpr(node) as OldExpr;
                // And back out again
                InOldExpr = false;

                // Remove the OldExpr node by just returning its Expr
                return result.Expr;
            }


        }

    }
}

