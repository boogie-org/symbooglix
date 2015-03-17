// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 8 %symbooglix --output-dir %t.symbooglix-out --solver=DUMMY %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithDisallowedSpeculativePath 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtUnsatisfiableAxiom 0
// RUN: %ctcy %t.symbooglix-out/termination_counters_ONLY_SPECULATIVE.yml TerminatedWithoutError 0
// RUN: %ctcy %t.symbooglix-out/termination_counters_ONLY_SPECULATIVE.yml TerminatedWithDisallowedSpeculativePath 0
// RUN: %ctcy %t.symbooglix-out/termination_counters_ONLY_SPECULATIVE.yml TerminatedAtUnsatisfiableAxiom 1
const g:int;

// We expect that the Dummy solve will say the satisfiability
// of this axiom is UNKNOWN.
axiom g > 0;

procedure main()
{
   var b:bool;

   // Need to use g other globalDDE will remove it
   b := g > 0;
   return;
}
