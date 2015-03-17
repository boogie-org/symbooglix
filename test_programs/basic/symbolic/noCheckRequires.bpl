// RUN: %rmdir %t.symbooglix-out
// RUN: %eec 0 %symbooglix --output-dir %t.symbooglix-out --check-entry-requires=0 %s
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithoutError 1
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtUnsatisfiableAxiom 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedAtFailingAssert 0
// RUN: %ctcy %t.symbooglix-out/termination_counters.yml TerminatedWithDisallowedSpeculativePath 0
// These declarations are taken from a SMACK generated boogie program
type float;
function $fp2si(f:float) returns (int);
function $si2fp(i:int) returns (float);
procedure main()
requires (forall i: int :: $fp2si($si2fp(i)) == i);
{
    var x:int;
    assert x == $fp2si($si2fp(x));
}
